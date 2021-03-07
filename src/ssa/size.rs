#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size {
    pub ptrs: usize,
    pub bytes: usize,
}

impl Default for Size {
    fn default() -> Size {
        Size::zero()
    }
}

impl std::ops::Add for Size {
    type Output = Size;

    fn add(self, rhs: Size) -> Size {
        Size {
            ptrs: self.ptrs + rhs.ptrs,
            bytes: self.bytes + rhs.bytes,
        }
    }
}

impl std::ops::AddAssign for Size {
    fn add_assign(&mut self, rhs: Self) {
        self.ptrs += rhs.ptrs;
        self.bytes += rhs.bytes;
    }
}

impl std::ops::Mul for Size {
    type Output = Size;

    fn mul(self, rhs: Self) -> Self::Output {
        Size {
            ptrs: self.ptrs * rhs.ptrs,
            bytes: self.bytes * rhs.bytes,
        }
    }
}

impl std::ops::Mul<usize> for Size {
    type Output = Size;

    fn mul(self, rhs: usize) -> Self::Output {
        Size {
            ptrs: self.ptrs * rhs,
            bytes: self.bytes * rhs,
        }
    }
}

impl std::ops::MulAssign for Size {
    fn mul_assign(&mut self, rhs: Self) {
        self.ptrs *= rhs.ptrs;
        self.bytes *= rhs.bytes;
    }
}

impl std::iter::Sum for Size {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut s = Size::default();
        for t in iter {
            s.ptrs += t.ptrs;
            s.bytes += t.bytes;
        }
        s
    }
}

impl std::fmt::Display for Size {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.ptrs == 0 && self.bytes == 0 {
            write!(f, "0")
        } else if self.ptrs == 0 {
            write!(f, "{} bytes", self.bytes)
        } else if self.bytes == 0 {
            write!(f, "{} ptrs", self.ptrs)
        } else {
            write!(f, "{} ptrs and {} bytes", self.ptrs, self.bytes)
        }
    }
}

impl Size {
    pub fn zero() -> Size {
        Size { ptrs: 0, bytes: 0 }
    }

    pub fn ptr() -> Size {
        Size { bytes: 0, ptrs: 1 }
    }

    pub fn bytes(bytes: usize) -> Size {
        Size { bytes, ptrs: 0 }
    }

    pub fn ptrs(ptrs: usize) -> Size {
        Size { bytes: 0, ptrs }
    }

    pub fn is_zero(&self) -> bool {
        self.ptrs == 0 && self.bytes == 0
    }
}
