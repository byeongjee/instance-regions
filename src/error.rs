use std::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    // The instance has no facts: rustc never borrow checks its body, its MIR is not
    // recorded, or the analysis leaves its kind of body out. A caller falls back to the
    // signature of the instance.
    Unavailable,
    // The instance has facts, but the analysis failed to compute them: a bug of the analysis
    // or of the build. A caller treats this as a failure.
    Internal,
}

// Why the facts of an instance cannot be computed.
#[derive(Clone, Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub reason: String,
}

impl Error {
    pub(crate) fn new(reason: impl Into<String>) -> Self {
        Self { kind: ErrorKind::Internal, reason: reason.into() }
    }

    pub(crate) fn unavailable(reason: impl Into<String>) -> Self {
        Self { kind: ErrorKind::Unavailable, reason: reason.into() }
    }

    pub fn is_unavailable(&self) -> bool {
        self.kind == ErrorKind::Unavailable
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.reason)
    }
}

impl From<preborrowck_mir::Error> for Error {
    fn from(error: preborrowck_mir::Error) -> Self {
        let kind: ErrorKind = match error.kind {
            preborrowck_mir::ErrorKind::Unavailable => ErrorKind::Unavailable,
            preborrowck_mir::ErrorKind::Internal => ErrorKind::Internal,
        };
        Self { kind, reason: error.reason }
    }
}

impl std::error::Error for Error {}
