#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Variance {
    Constant,
    Covariant,
    Contravariant,
    Invariant,
}

impl Default for Variance {
    fn default() -> Variance {
        Variance::Constant
    }
}

impl Variance {
    pub fn invert(self) -> Variance {
        match self {
            Variance::Contravariant => Variance::Covariant,
            Variance::Covariant => Variance::Contravariant,
            _ => self,
        }
    }

    pub fn concat(self, other: Variance) -> Variance {
        use Variance::*;
        match (self, other) {
            (Constant, _) => other,
            (_, Constant) => self,
            (Covariant, Covariant) => Covariant,
            (Contravariant, Contravariant) => Contravariant,
            _ => Invariant,
        }
    }
}
