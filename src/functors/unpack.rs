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
