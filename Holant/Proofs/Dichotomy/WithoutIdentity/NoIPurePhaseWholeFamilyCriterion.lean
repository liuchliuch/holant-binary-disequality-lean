import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyGraph
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativePhaseCriterion
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeProductCriterion

/-! One common chart on the actual nonzero-row tensor supplies a common
native basis for every original table row, including the native edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyCriterion
open Holant Holant.Tractable Holant.Algebraic
namespace G
export NoIPurePhaseWholeFamilyGraph (row wholeValue all_rows)
end G
namespace W
export NoIPurePhaseWholeFamily (twist)
end W
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K:=K.algebra'
variable {s : ℕ} {a : ℕ→ℕ} (H : (i : Fin s)→Signature K (a i.val))

def family : SignatureFamily AlgebraicComplex:=Set.range (fun i : Fin s=>(⟨a i.val,G.row K H i⟩ : AnySignature AlgebraicComplex))

theorem phase (r : AlgebraicComplex) (nonzero : r≠0)
    (good : Affine (W.twist r (G.wholeValue K H))) :
    TractX (familyAction sourceKBasis (family K H)) := by
  apply NoINativePhaseCriterion.criterion _ (Set.finite_range _) r nonzero
  rintro _ ⟨j,rfl⟩
  exact G.all_rows K H .affine r nonzero good j

theorem unit_twist {n : ℕ} (f : Signature AlgebraicComplex n) : W.twist 1 f=f := by
  funext z
  change (1 : AlgebraicComplex)^(weight z)*f z=f z
  simp

theorem product (good : Product (G.wholeValue K H)) :
    TractX (familyAction sourceKBasis (family K H)) := by
  apply NoINativeProductCriterion.criterion _ (Set.finite_range _)
  rintro _ ⟨j,rfl⟩
  have hg : Product (W.twist 1 (G.wholeValue K H)) := by
    rwa [unit_twist]
  have result:=G.all_rows K H .product 1 one_ne_zero hg j
  change Product (W.twist 1 (G.row K H j)) at result
  rwa [unit_twist] at result

/-- The chosen phase remains outside the universal over all family rows. -/
theorem classified {α : Type} (phaseValues : α→AlgebraicComplex)
    (nonzero : ∀i,phaseValues i≠0)
    (good : (∃i,Affine (W.twist (phaseValues i) (G.wholeValue K H))) ∨
      Product (G.wholeValue K H)) :
    TractX (familyAction sourceKBasis (family K H)) := by
  rcases good with ⟨i,hi⟩|hp
  · exact phase K H (phaseValues i) (nonzero i) hi
  · exact product K H hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyCriterion
end
