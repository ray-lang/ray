#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variance {
    Constant,
    Covariant,
    Contravariant,
    Invariant,
}

impl Variance {
    pub fn concat(self, other: Variance) -> Variance {
        match (self, other) {
            (Variance::Constant, _) => other,
            (_, Variance::Constant) => self,
            _ if self == other => self,
            _ => Variance::Invariant
        }
    }

    pub fn invert(self) -> Variance {
        match self {
            Variance::Covariant => Variance::Contravariant,
            Variance::Contravariant => Variance::Covariant,
            _ => self,
        }
    }
}
