import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedSignedRows

/-! Positive port substitutions use no antidiagonal vertices. Their exact
weighted-source multiplier is one, independently of the anti phases. This
lets the genuine parity-correction recipes operate after an origin marking. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXUnsignedRows
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word arity)
open scoped BigOperators
namespace W
export NoXWeightedSignedPorts (weight portWeight table)
export NoXWeightedSignedRows (block ambient_value)
end W
namespace P
export OrdinaryNegativeSignedRowsPins (signedCompose lifted)
export OrdinaryNegativeSignedRowsCore (flatten)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n N m r : ℕ}

def Positive (ps : Fin n→Port m) : Prop := ∀i j,ps i≠.inr (j,true)

variable {K : Type} [Field K]
theorem weight_one (v w : K) (ps : Fin n→Port m) (positive : Positive ps) (z : Fin m→Bool) :
    W.weight v w ps z=1 := by
  apply Finset.prod_eq_one
  intro i _
  cases h : ps i with
  | inl bit=>rfl
  | inr pair=>
      rcases pair with ⟨j,sgn⟩
      cases sgn
      · rfl
      · exact False.elim (positive i j h)

theorem compose_positive (pins : Fin N→Bool ⊕ Fin n) (ps : Fin n→Port m) (positive : Positive ps) :
    Positive (P.signedCompose pins ps) := by
  intro i j he
  cases hp : pins i with
  | inl bit=>simp [P.signedCompose,hp] at he
  | inr q=>exact positive q j (by simpa only [P.signedCompose,hp,Sum.elim_inr] using he)

theorem flatten_positive (ps : Fin r→Fin n→Port m) (positive : ∀i,Positive (ps i)) :
    Positive (P.flatten ps) := fun i j=>positive (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 j

section Source
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (f : Signature K N) (v w : K)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,W.table f v w i⟩)
variable (pins : Fin N→Bool ⊕ Fin n) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (ps : Fin r→Fin n→Port m)
variable (even : ∀j,Even (∑i,OrdinaryNegativeSignedPortsIncidence.bundleSize (ps i) j))
variable (positive : ∀i,Positive (ps i))

include positive in
theorem ambient_value (z : Fin m→Bool) :
    ((W.block H labels f v w literal pins pure ps even).signature H z : AlgebraicComplex)=
      ∏i,OrdinaryNegativeSparseMinimalRank.row f pins (word (ps i) z) := by
  rw [W.ambient_value]
  have hp : Positive (P.flatten (P.lifted pins ps)) :=
    flatten_positive _ (fun i=>compose_positive pins (ps i) (positive i))
  rw [weight_one (v : AlgebraicComplex) (w : AlgebraicComplex) (P.flatten (P.lifted pins ps)) hp z,one_mul]

include literal pure even positive in
theorem evenBad (bad : ¬Affine (fun z=>∏i,OrdinaryNegativeSparseMinimalRank.row f pins (word (ps i) z))) :
    OrdinaryNegativeXUniversalResource.EvenBad H := by
  refine ⟨m,W.block H labels f v w literal pins pure ps even,?_⟩
  intro ha
  exact bad (by simpa only [ambient_value H labels f v w literal pins pure ps even positive] using ha)
end Source


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXUnsignedRows
end
