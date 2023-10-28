use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::iter::zip;
use std::rc::Rc;

/* WARNING: EVIL SPAGHETTI AHEAD*/

pub trait Unpack: Sized {
    type StepData;
    fn un_step(self) -> (Self::StepData, Vec<Self>);

    fn build_no_clone<T, F>(self, f: F) -> T where F: Fn(Self::StepData, Vec<T>) -> T {
        self.build_f_ref(&f)
    }
    fn build<T, F>(self, f: F) -> T where F: Fn(Self::StepData, Vec<T>) -> T, T: Clone {
        self.build_no_clone(f)
    }
}

trait UnpackImpl: Unpack{
    fn build_f_ref<T, F>(self, f: &F) -> T where F: Fn(Self::StepData, Vec<T>) -> T {
        let (data, sub_objects) = self.un_step();
        let mut sub_ts = vec![];
        for x in sub_objects.into_iter(){
            sub_ts.push(x.build_f_ref(f));
        }
        f(data, sub_ts)
    }
}

impl<T: Unpack> UnpackImpl for T {}

pub trait UnpackRc: Sized {
    type StepData;
    type Step;
    fn get_rc(&self) -> Rc<Self::Step>;
    fn get_rc_mut(&mut self) -> &mut Rc<Self::Step>;
    fn into_rc(self) -> Rc<Self::Step>{
        (&self).get_rc().clone()
    }
    fn un_step_data(this: &Self::Step) -> Self::StepData;
    fn un_step_subs(this: &Self::Step) -> Vec<Self>;
}

pub trait UnpackRcDrop: UnpackRc {

    fn drop_reference(top_ptr: &mut Rc<Self::Step>) {
        // If you force the sub-objects to be dropped after the top,
        // there is no possibility of Rc drop recursion.
        if Rc::strong_count(top_ptr) == 1 {
            let mut stack = vec![top_ptr.clone()];
            while let Some(mut ptr) = stack.pop() {
                if Rc::ptr_eq(&ptr, top_ptr) && Rc::strong_count(&ptr) == 2 {
                    ptr = Self::shuffle_pointer(top_ptr);
                }
                if let Some(step) = Rc::into_inner(ptr) {
                    let subs= Self::un_step_subs(&step);
                    // step deleted at this point
                    for sub in subs {
                        stack.push(sub.into_rc());
                    }
                }
            }
        }
    }
}
trait UnpackRcDropImpl: UnpackRcDrop {
    fn shuffle_pointer(ptr: &mut Rc<Self::Step>) -> Rc<Self::Step>{
        let subs = Self::un_step_subs(ptr);
        if let Some(sub) = subs.last() {
            std::mem::replace::<Rc<Self::Step>>(ptr, sub.get_rc())
        }
        else {
            ptr.clone()
        }
    }
}

impl<T: UnpackRc> Unpack for T {
    type StepData = T::StepData;

    fn un_step(self) -> (Self::StepData, Vec<Self>) {
        (Self::un_step_data(&self.get_rc()), Self::un_step_subs(&self.get_rc()))
    }

    fn build_no_clone<S, F>(self, f: F) -> S where F: Fn(Self::StepData, Vec<S>) -> S,{
        enum State<R: UnpackRc> {
            Open(Rc<R::Step>, usize, usize), // step, return_pointer, index
            Close(R::StepData ,usize, usize, usize), // arguments pointer, return pointers, index
        }
        let mut results: Vec<Vec<Option<S>>> = vec![vec![None]];
        let mut stack: Vec<State<T>> = vec![State::Open(self.into_rc(), 0, 0)];
        while let Some(item) = stack.pop() {
            match item {
                State::Open(step_ptr, ret, index) => {
                    let arg = results.len();
                    stack.push(State::Close(
                        T::un_step_data(&*step_ptr),
                        arg,
                        ret,
                        index,
                    ));
                    let subs = T::un_step_subs(&*step_ptr);
                    results.push(
                        std::iter::repeat_with(|| None).take(subs.len()).collect()
                    );
                    for (index, sub) in zip(0.., subs) {
                        stack.push(State::Open(
                            sub.into_rc(),
                            arg,
                            index,
                        ));
                    }
                }
                State::Close(step_data, args, ret, index) => {
                    results[ret][index] = Some(
                        f(
                            step_data,
                            results[args]
                                .iter_mut()
                                .map(
                                    |p| p.take().unwrap()
                                )
                                .collect()
                        )
                    )
                }
            }
        }
        results[0][0].take().unwrap()
    }

    fn build<S, F>(self, f: F) -> S where F: Fn(Self::StepData, Vec<S>) -> S, S: Clone {
        struct HashWrapper<R>(Rc<R>);
        impl<R> Hash for HashWrapper<R> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                std::ptr::hash(&*self.0, state)
            }
        }
        impl<R> PartialEq for HashWrapper<R> {
            fn eq(&self, other: &Self) -> bool {
                Rc::ptr_eq(&self.0, &other.0)
            }
        }
        impl<R> Eq for HashWrapper<R> {}
        let mut results: HashMap<HashWrapper<T::Step>, S> = HashMap::new();

        enum State<R: UnpackRc> {
            Open(Rc<R::Step>),
            Close(Rc<R::Step>, R::StepData, Vec<Rc<R::Step>>),
        }
        // results.insert(HashWrapper(self.get_rc().clone()), vec![None]);
        let top_ptr = self.into_rc();
        let mut stack:Vec<State<T>> = vec![State::Open(top_ptr.clone())];
        while let Some(state) = stack.pop() {
            match state {
                State::Open(ptr) => {
                    if ! results.contains_key(&HashWrapper::<T::Step>(Rc::<T::Step>::clone(&ptr))) {
                        let dat = T::un_step_data(&*ptr);
                        let subs: Vec<Rc<T::Step>> = T::un_step_subs(&*ptr)
                            .into_iter()
                            .map(|e| e.into_rc())
                            .collect();
                        stack.push(State::Close(ptr.clone(), dat, subs.clone()));
                        for sub in subs {
                            stack.push(State::Open(sub));
                        }
                    }
                }
                State::Close(ptr, dat, subs) => {
                    results.insert(
                        HashWrapper(ptr.clone()),
                        f(dat,
                          subs.into_iter()
                              .map(|p| results[&HashWrapper(p)].clone())
                              .collect()
                        )
                    );
                }
            }
        }
        results[&HashWrapper(top_ptr)].clone()
    }
}
impl<T: UnpackRcDrop> UnpackRcDropImpl for T {}
#[macro_export]
macro_rules! unpack_drop {
    ( $name:ident $(< $( $lt:tt $( : $clt:tt $(+ $dlt:tt )* )? ),+ >)? ) => {
        impl $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)? UnpackRcDrop for $name $(< $( $lt ),+ >)? {}
        impl $(< $( $lt $( : $clt $(+ $dlt )* )? ),+ >)?
            Drop
        for $name $(< $( $lt ),+ >)?
        {
            fn drop(&mut self) {
                Self::drop_reference(self.get_rc_mut());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use ntest::timeout;
    use super::*;
    #[derive(Debug, PartialEq, Eq)]
    enum BinaryTreeStep{
        Leaf,
        Node(BinaryTree, BinaryTree),
    }
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct BinaryTree{
        step: Rc<BinaryTreeStep>
    }

    impl BinaryTree {
        fn new_leaf() -> Self {
            BinaryTree { step: Rc::new(BinaryTreeStep::Leaf) }
        }

        fn new_node(l: Self, r: Self) -> Self {
            BinaryTree { step: Rc::new(BinaryTreeStep::Node(l, r)) }
        }
    }

    enum BinaryTreeStepData{
        Leaf,
        Node,
    }

    struct RecursiveUnpack(BinaryTree);
    impl Unpack for RecursiveUnpack{
        type StepData = BinaryTreeStepData;

        fn un_step(self) -> (Self::StepData, Vec<Self>) {
            match &*self.0.step {
                BinaryTreeStep::Leaf => {(BinaryTreeStepData::Leaf, vec![])},
                BinaryTreeStep::Node(l, r) => {
                    (BinaryTreeStepData::Node,
                     vec![
                         RecursiveUnpack(l.clone()),
                         RecursiveUnpack(r.clone()),
                     ])
                },
            }
        }
    }

    struct UnRecursiveUnpack(BinaryTree);
    unpack_drop!(UnRecursiveUnpack);
    impl UnpackRc for UnRecursiveUnpack {
        type StepData = BinaryTreeStepData;
        type Step = BinaryTreeStep;
        fn get_rc(&self) -> Rc<Self::Step> {
            (&self.0.step).clone()
        }
        fn get_rc_mut(&mut self) -> &mut Rc<Self::Step> {
            &mut self.0.step
        }
        fn un_step_data(this: &Self::Step) -> Self::StepData {
            match this {
                BinaryTreeStep::Leaf => { BinaryTreeStepData::Leaf }
                BinaryTreeStep::Node(_, _) => { BinaryTreeStepData::Node }
            }
        }
        fn un_step_subs(this: &Self::Step) -> Vec<Self> {
            match this {
                BinaryTreeStep::Leaf => { vec![] }
                BinaryTreeStep::Node(l, r) => {
                    vec![
                        UnRecursiveUnpack(l.clone()),
                        UnRecursiveUnpack(r.clone()),
                    ]
                }
            }
        }
    }

    fn fib(n: usize) -> u128 {
        if n == 0 { return 0;}
        (0..(n - 1)).fold((0, 1), |(a, b), _| (b, a + b)).1
    }
    fn fib_tree(n: usize) -> BinaryTree {
        if n == 0 { panic!() }
        if n == 1 { return BinaryTree::new_leaf(); }
        (0..(n - 2))
            .fold(
                (BinaryTree::new_leaf(), BinaryTree::new_leaf()),
                |(a, b), _| (b.clone(), BinaryTree::new_node(a, b))
            ).1
    }
    fn unary_tree(n: usize) -> BinaryTree {
        (0..n)
            .fold(
                BinaryTree::new_leaf(),
                |a, _| BinaryTree::new_node(a, BinaryTree::new_leaf())
            )
    }
    fn count_step(dat: BinaryTreeStepData, sub_counts: Vec<u128>) -> u128 {
        match dat {
            BinaryTreeStepData::Leaf => {1}
            BinaryTreeStepData::Node => {sub_counts[0] + sub_counts[1]}
        }
    }
    fn depth_step(dat: BinaryTreeStepData, sub_counts: Vec<usize>) -> usize {
        match dat {
            BinaryTreeStepData::Leaf => {0}
            BinaryTreeStepData::Node => {std::cmp::max(sub_counts[0], sub_counts[1]) + 1}
        }
    }
    #[test]
    fn stack_drop_breaker() {
        let tree = fib_tree(1_usize << 16);
        let d = UnRecursiveUnpack(tree.clone());
        assert!(matches!(&*tree.step, BinaryTreeStep::Node(_, _)));
        drop(tree);
        drop(d);
    }
    #[test]
    fn stack_build_breaker() {
        let depth = 1_usize << 16;
        let tree = unary_tree(depth);
        assert_eq!(UnRecursiveUnpack(tree.clone()).build(depth_step), depth);
        assert_eq!(UnRecursiveUnpack(tree.clone()).build_no_clone(depth_step), depth);
        drop(UnRecursiveUnpack(tree));
    }
    #[test]
    #[timeout(100)]
    fn runtime_build_breaker() {
        let tree = UnRecursiveUnpack(fib_tree(128));
        assert_eq!(fib(128), tree.build(count_step));
    }

    #[test]
    fn test_fib() {
        assert_eq!(fib(0), 0);
        assert_eq!(fib(1), 1);
        assert_eq!(fib(2), 1);
        assert_eq!(fib(3), 2);
        assert_eq!(fib(4), 3);
        assert_eq!(fib(5), 5);
        assert_eq!(fib(6), 8);
        assert_eq!(fib(47), 2_971_215_073_u128);
        assert_eq!(fib(128), 251728825683549488150424261_u128);
    }
    #[test]
    fn test_fib_tree() {
        assert_eq!(fib_tree(2), BinaryTree::new_leaf());
        assert_eq!(fib_tree(3),
                   BinaryTree::new_node(
                       BinaryTree::new_leaf(),
                       BinaryTree::new_leaf(),
                   )
        );
    }
    #[test]
    fn test_fib_tree_counts() {
        assert_eq!(RecursiveUnpack(BinaryTree::new_leaf()).build(count_step), 1_u128);
        assert_eq!(RecursiveUnpack(fib_tree(10)).build_no_clone(count_step), fib(10));
        assert_eq!(RecursiveUnpack(fib_tree(10)).build(depth_step), 8);
    }
    #[test]
    fn test_unary_depth() {
        assert_eq!(RecursiveUnpack(unary_tree(10)).build(depth_step), 10);
    }
}