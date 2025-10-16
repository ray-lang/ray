macro_rules! expect_if {
    ($self:ident, $( $pattern:pat_param )|+ $( if $guard: expr )?) => {
        match $self.peek_kind() {
            $( $pattern )|+ $( if $guard )? => {
                $self.lex.consume();
                true
            },
            _ => false
        }
    }
}

macro_rules! peek {
    ($self:ident, $( $pattern:pat_param )|+ $( if $guard: expr )?) => {
        match $self.peek_kind() {
            $( $pattern )|+ $( if $guard )? => true,
            _ => false
        }
    }
}

macro_rules! must_peek {
    ($self:ident, $( $pattern:pat_param )|+ $( if $guard: expr )?) => {
        match $self.must_peek_kind()? {
            $( $pattern )|+ $( if $guard )? => true,
            _ => false
        }
    }
}
