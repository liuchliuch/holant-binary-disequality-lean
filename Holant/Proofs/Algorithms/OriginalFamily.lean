import Holant.Proofs.Algorithms.CommonFieldTables
import Holant.Tractable.Scalars
import Holant.Kernel


namespace Holant.LocalDrafts.MainChain.OriginalFamily
open Holant.Tractable Holant.Algebraic Holant.Complexity
open ExactSignatureTables FixedGadgetSubstitution
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (E : Fin b → Kernel AlgebraicComplex)

def coefficient : CoefficientIndex s b arity → AlgebraicComplex
  | .inl ⟨i,x⟩ => G i x
  | .inr (i,u,v) => E i u v

theorem coefficient_algebraic (a : CoefficientIndex s b arity) :
    IsAlgebraic ℚ (coefficient G E a) := Algebra.IsAlgebraic.isAlgebraic _

abbrev presentation := familyPresentation (coefficient G E) (coefficient_algebraic G E)
abbrev tables := CommonFieldTables.originalTables (coefficient G E) (coefficient_algebraic G E)
abbrev value := (tables G E).evaluate (presentation G E)

theorem value_exact (r : ExactSignatureTables.Input s b arity) :
    (value G E r : AlgebraicComplex)=(r.val.realize r.property G E).denote Fin.elim0 := by
  simpa only [value,tables,CommonFieldTables.originalTables,coefficient,id_eq] using
    PresentedScaledFamily.target_value_exact (coefficient G E) (coefficient_algebraic G E) id r

end
end Holant.LocalDrafts.MainChain.OriginalFamily
