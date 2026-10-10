/-! Balanced literal finite tables for certificate data. Lookup follows a
stored binary tree; checked finite callers provide its intended index range. -/
universe u
namespace Holant.Pauli.ExoticKlein.SixPort

inductive FiniteTable (A : Type u) where
  | leaf : A → FiniteTable A
  | branch : FiniteTable A → FiniteTable A → FiniteTable A

namespace FiniteTable

def get {A : Type u} : FiniteTable A → Nat → A
  | .leaf value,_ => value
  | .branch left right,index => if index % 2 = 0 then get left (index/2) else get right (index/2)

end FiniteTable
end Holant.Pauli.ExoticKlein.SixPort
