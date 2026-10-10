import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedSource

/-! A signed substitution with separately even positive and negative counts
already supplies an unsigned even nonaffine block. Opposite assignments are
used only in the Affine pullback proof, never as a physical gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionEvenProjection
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSignedPortsCore (Port word)
namespace P
export NoXSeparateSignedProjection (signedCount constant_count positive_count negative_count opposite_value)
end P
namespace S
export NoXSeparateSignedSource (rows ports_exact)
end S
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s m : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (ps : Fin (b j.val)→Port m)
variable (even : ∀q bit,Even (P.signedCount ps q bit))

include even in
theorem balanced : EvenRecipe (S.rows H j p0 p1 h0 h1 ps) := by
  intro i q
  have hi : i=0 := Fin.eq_zero i
  subst i
  rw [S.ports_exact]
  cases q with
  | inl bit=>rw [P.constant_count];exact Even.mul_right (by decide : Even 2) _
  | inr q=>
    refine Fin.addCases ?_ ?_ q
    · intro k;rw [P.positive_count];exact even k false
    · intro k;rw [P.negative_count];exact even k true

def block : B.Block (s:=s) (b:=b) (m+m) :=
  ⟨0,S.rows H j p0 p1 h0 h1 ps,balanced H j p0 p1 h0 h1 ps even⟩

def opposite (z : Fin m→Bool) : Fin (m+m)→Bool := Fin.addCases z (fun i=>!(z i))

theorem opposite_affine : TwoTranslate.IsAffineMap (opposite (m:=m)) := by
  intro x y
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [opposite,AffinePhase.xor,AffinePhase.origin,Fin.addCases_left]
    cases x i <;> cases y i <;> rfl
  · intro i
    simp only [opposite,AffinePhase.xor,AffinePhase.origin,Fin.addCases_right]
    cases x i <;> cases y i <;> rfl

theorem value (z : Fin m→Bool) :
    (block H j p0 p1 h0 h1 ps even).signature H (opposite z)=H j (word ps z) := by
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>m+m) H 0
    (S.rows H j p0 p1 h0 h1 ps) 0 (opposite z)=_
  rw [OrdinaryNegativeSparseMixingSource.trace_zero,S.rows,
    OrdinaryNegativeMixedBlockRelabel.coefficient_eq]
  exact P.opposite_value (H j) ps z

include even h0 h1 in
theorem evenBad (bad : ¬Affine (fun z=>(H j (word ps z) : AlgebraicComplex))) : B.EvenBad H := by
  refine ⟨m+m,block H j p0 p1 h0 h1 ps even,?_⟩
  intro aff
  have pulled:=aff.precompose opposite (opposite_affine (m:=m))
  apply bad
  simpa only [value] using pulled

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionEvenProjection
end
