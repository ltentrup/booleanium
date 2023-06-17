const RESIZE_INTERVAL: usize = 10;

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Restart {
    counter: usize,
}

impl Restart {
    pub(crate) fn should_do_restart(&mut self) -> bool {
        self.counter += 1;
        self.counter % RESIZE_INTERVAL == 0
    }
}
