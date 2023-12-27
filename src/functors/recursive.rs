use std::rc::Rc;
use std::hash::{Hash, Hasher};
use std::collections::HashMap;
use std::io::Write;
use crate::functors::unpack::Unpack;

pub trait UnpackRc: Sized{
    type StepData;
    type StepRef;
    fn rc(&self) -> &Rc<Self::StepRef>;
    fn un_step_data(&self) -> Self::StepData;
    fn un_step_subs(&self) -> Vec<Self>;
}

struct StepState<R, B, D> {
    results: Vec<R>,
    step_data: D,
    subs: <Vec<B> as IntoIterator>::IntoIter,
}
enum State<R, B, D, P> {
    Open(B),
    OpenStep(StepState<R, B, D>),
    CloseStep(Rc<P>, StepState<R, B, D>),
}
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnpackRcWrapper<T: UnpackRc>{
    internal: T,
}

impl<T: UnpackRc> UnpackRcWrapper<T> {
    pub fn new(internal: T) -> Self{
        UnpackRcWrapper {internal}
    }
    pub fn internal(&self) -> &T {&self.internal}
    // pub fn into_internal(self) -> T {self.internal}
    pub fn un_step_data(&self) -> T::StepData {
        self.internal.un_step_data()
    }

    pub fn un_step_subs(&self) -> Vec<Self> {
        T::un_step_subs(&self.internal)
            .into_iter()
            .map(
                |x| UnpackRcWrapper::<T>::new(x)
            )
            .collect()
    }

    fn drop_update_stack(cur: &T, stack: &mut Vec<(T, Rc<T::StepRef>)>) {
        let mut subs = cur.un_step_subs();
        while let Some(x) = subs.pop() {
            let x_ptr = x.rc().clone();
            stack.push((x, x_ptr));
        }
    }
    fn drop_shuffle_pointer(&mut self) -> Option<T>{
        let mut subs = self.internal.un_step_subs();
        if let Some(sub) = subs.pop() {
            Some(std::mem::replace::<T>(&mut self.internal, sub))
        }
        else { None }
    }
    fn drop_impl_step(
        &mut self,
        mut stack: &mut Vec<(T, Rc<T::StepRef>)>,
        x: T,
        ptr: Rc<T::StepRef>
    ) {
        if Rc::ptr_eq(self.internal.rc(), x.rc()) && Rc::strong_count(&ptr) == 3 {
            self.drop_shuffle_pointer();
        }
        if Rc::strong_count(&ptr) != 2 {
            return;
        }
        UnpackRcWrapper::drop_update_stack(&x, &mut stack);
        drop(x);
        drop(ptr);
    }

    fn handle_open_state<S>(stack: &mut Vec<State<S, Self, T::StepData, T::StepRef>>, x: Self) {
        stack.push(
            State::OpenStep(
                StepState {
                    results: vec![],
                    step_data: x.un_step_data(),
                    subs: x.un_step_subs().into_iter(),
                }
            )
        );
    }
    fn handle_open_step_state<S, F>(
        f: &F,
        stack: &mut Vec<State<S, Self, T::StepData, T::StepRef>>,
        ret: &mut Option<S>,
        state: StepState<S, Self, T::StepData>
    ) where F: Fn(T::StepData, Vec<S>) -> S {
        let StepState { results, step_data, mut subs } = state;
        if let Some(sub) = subs.next() {
            stack.push(
                State::CloseStep(
                    sub.internal.rc().clone(),
                    StepState { results, step_data, subs, }
                )
            );
            stack.push(State::Open(sub));
        } else {
            let none_ish = ret.replace(f(step_data, results));
            debug_assert!(none_ish.is_none());
        }
    }
    fn handle_close_step_state<S>(
        stack: &mut Vec<State<S, Self, T::StepData, T::StepRef>>,
        state: StepState<S, Self, T::StepData>,
        returned: S
    ) {
        let StepState {
            mut results,
            step_data,
            subs,
        } = state;
        results.push(returned);
        stack.push(State::OpenStep(StepState { results, step_data, subs }));
    }
}

impl<T: UnpackRc> Unpack for UnpackRcWrapper<T> {
    type StepData = T::StepData;

    fn un_step(self) -> (Self::StepData, Vec<Self>) {
        (
            self.un_step_data(),
            self.un_step_subs(),
        )
    }

    fn build_no_clone<S, F>(self, f: F) -> S where F: Fn(Self::StepData, Vec<S>) -> S {
        let mut stack = vec![State::<S, Self, T::StepData, T::StepRef>::Open(self)];
        let mut ret: Option<S> = None;
        while let Some(state) = stack.pop() {
            match state {
                State::Open(x) => { Self::handle_open_state(&mut stack, x); }
                State::OpenStep(state) => {
                    Self::handle_open_step_state(&f, &mut stack, &mut ret, state);
                }
                State::CloseStep(_, state) => {
                    let returned = ret.take().unwrap();
                    Self::handle_close_step_state(&mut stack, state, returned);
                }
            }
        }
        ret.take().unwrap()
    }

    fn build<S, F>(self, f: F) -> S where F: Fn(Self::StepData, Vec<S>) -> S, S: Clone {
        let mut result_table: HashMap<HashWrapper<T::StepRef>, S> = HashMap::new();
        let mut stack = vec![State::<S, Self, T::StepData, T::StepRef>::Open(self)];
        let mut ret: Option<S> = None;
        while let Some(state) = stack.pop() {
            match state {
                State::Open(x) => {
                    let key = HashWrapper::<T::StepRef>(x.internal.rc().clone());
                    if let Some(to_ret) = result_table.get(&key) {
                        debug_assert!(ret.replace(to_ret.clone()).is_none());
                    } else {
                        Self::handle_open_state(&mut stack, x);
                    }
                }
                State::OpenStep(state) => {
                    Self::handle_open_step_state(&f, &mut stack, &mut ret, state);
                }
                State::CloseStep(seek, state) => {
                    let returned = ret.take().unwrap();
                    result_table.insert(HashWrapper::<T::StepRef>(seek), returned.clone());
                    Self::handle_close_step_state(&mut stack, state, returned);
                }
            }
        }
        ret.take().unwrap()
    }
}

impl<T:UnpackRc> Drop for UnpackRcWrapper<T> {
    fn drop(&mut self) {
        // If you force the sub-objects to be dropped after the top,
        // there is no possibility of Rc drop recursion.
        if Rc::strong_count(self.internal.rc()) == 1 {
            let maybe_this = self.drop_shuffle_pointer();
            if let Some(this) = maybe_this {
                let this_ptr = this.rc().clone();
                let mut stack = vec![(this, this_ptr)];
                while let Some((x, ptr)) = stack.pop() {
                    self.drop_impl_step(&mut stack, x, ptr);
                }
            }
        }
    }
}

#[cfg(test)]
pub (in crate::functors) mod tests {
    use std::rc::Rc;
    use ntest::timeout;
    use crate::functors::unpack::Unpack;
    use super::*;
    #[derive(Debug, PartialEq, Eq)]
    enum BinaryTreeStep{
        Leaf,
        Node(BinaryTree, BinaryTree),
    }
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct BinaryTree{
        step: Rc<BinaryTreeStep>
    }

    impl BinaryTree {
        pub fn new_leaf() -> Self {
            BinaryTree { step: Rc::new(BinaryTreeStep::Leaf) }
        }

        pub fn new_node(l: Self, r: Self) -> Self {
            BinaryTree { step: Rc::new(BinaryTreeStep::Node(l, r)) }
        }
    }

    pub enum BinaryTreeStepData{
        Leaf,
        Node,
    }

    pub struct RecursiveUnpack(BinaryTree);
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
    #[derive(Clone)]
    struct UnRecursiveUnpack(BinaryTree);
    impl UnpackRc for UnRecursiveUnpack {
        type StepData = BinaryTreeStepData;
        type StepRef = BinaryTreeStep;
        fn rc(&self) -> &Rc<Self::StepRef> {
            &self.0.step
        }
        fn un_step_data(&self) -> Self::StepData {
            match *self.0.step {
                BinaryTreeStep::Leaf => { BinaryTreeStepData::Leaf }
                BinaryTreeStep::Node(_, _) => { BinaryTreeStepData::Node }
            }
        }
        fn un_step_subs(&self) -> Vec<Self> {
            match &*self.0.step {
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
    // unpack_drop!(UnRecursiveUnpack);

    pub fn fib(n: usize) -> u128 {
        if n == 0 { return 0;}
        (0..(n - 1)).fold((0, 1), |(a, b), _| (b, a + b)).1
    }
    pub fn fib_tree(n: usize) -> BinaryTree {
        if n == 0 { panic!() }
        if n == 1 { return BinaryTree::new_leaf(); }
        (0..(n - 2))
            .fold(
                (BinaryTree::new_leaf(), BinaryTree::new_leaf()),
                |(a, b), _| (b.clone(), BinaryTree::new_node(a, b))
            ).1
    }
    pub fn unary_tree(n: usize) -> BinaryTree {
        (0..n)
            .fold(
                BinaryTree::new_leaf(),
                |a, _| BinaryTree::new_node(a, BinaryTree::new_leaf())
            )
    }
    pub fn count_step(dat: BinaryTreeStepData, sub_counts: Vec<u128>) -> u128 {
        match dat {
            BinaryTreeStepData::Leaf => {1}
            BinaryTreeStepData::Node => {sub_counts[0] + sub_counts[1]}
        }
    }
    pub fn depth_step(dat: BinaryTreeStepData, sub_counts: Vec<usize>) -> usize {
        match dat {
            BinaryTreeStepData::Leaf => {0}
            BinaryTreeStepData::Node => {std::cmp::max(sub_counts[0], sub_counts[1]) + 1}
        }
    }
    #[test]
    fn stack_drop_breaker() {
        std::io::stdout().flush().unwrap();
        let tree = fib_tree(1_usize << 16);
        let d = UnRecursiveUnpack(tree.clone());
        assert!(matches!(&*tree.step, BinaryTreeStep::Node(_, _)));
        drop(tree);
        drop(UnpackRcWrapper::new(d));
    }
    #[test]
    fn stack_build_breaker() {
        let depth = 1_usize << 16;
        let tree = UnpackRcWrapper::new(UnRecursiveUnpack(unary_tree(depth)));
        assert_eq!(tree.clone().build(depth_step), depth);
        assert_eq!(tree.clone().build_no_clone(depth_step), depth);
        drop(tree);
    }
    #[test]
    #[timeout(100)]
    fn runtime_build_breaker() {
        let tree = UnpackRcWrapper::new(UnRecursiveUnpack(fib_tree(128)));
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


    #[test]
    fn trivial() {
        let tree = BinaryTree::new_leaf();
        let wrapped = UnpackRcWrapper::new(UnRecursiveUnpack(tree));
        assert_eq!(1, 1);
        drop(wrapped);
    }
}