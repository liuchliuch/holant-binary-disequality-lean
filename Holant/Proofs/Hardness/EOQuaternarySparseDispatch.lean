import Holant.Proofs.Hardness.EOQuaternarySparseFourSource
import Holant.Proofs.Hardness.EOQuaternarySparseTract

/-! Exhaustive original-mask dispatch through size four. All masks outside
an opposite-pair affine plane have an actual EOTract certificate or the new
native-X counting producer. The remaining plane is stated explicitly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseDispatch
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace N
export EOQuaternarySparseFourLocal (mask index Applicable MaskCondition)
end N
namespace O
export FiveSupportEOOrdering (middleWord middleCoeff)
end O
namespace T
export EOQuaternarySparseTract (support FixedPort small_tract fixed_tract)
end T
set_option backward.isDefEq.respectTransparency false

private theorem middle_injective : Function.Injective O.middleWord := by decide
private theorem middle_surj : ∀x : Fin 4→Bool,weight x=2 → ∃i,O.middleWord i=x := by decide

def middleSupport (M : Signature AlgebraicComplex 4) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter fun i=>N.mask M i

theorem support_image (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M) :
    T.support M=(middleSupport M).image O.middleWord := by
  classical
  ext x
  simp only [EOQuaternarySparseTract.mem_support,Finset.mem_image]
  constructor
  · intro hx
    have hw : weight x=2 := by by_contra hn; exact hx (he x hn)
    obtain ⟨i,hi⟩ := middle_surj x hw
    refine ⟨i,?_,hi⟩
    simp only [middleSupport,Finset.mem_filter,Finset.mem_univ,true_and,N.mask,
      decide_eq_true_eq,O.middleCoeff,hi]
    exact hx
  · rintro ⟨i,hi,rfl⟩
    simpa only [middleSupport,Finset.mem_filter,Finset.mem_univ,true_and,N.mask,
      decide_eq_true_eq,O.middleCoeff] using hi

theorem support_card (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M) :
    (T.support M).card=(middleSupport M).card := by
  classical
  rw [support_image M he,Finset.card_image_of_injective _ middle_injective]

/-- The unresolved opposite-pair affine-plane branch, in original coefficients. -/
def Plane (M : Signature AlgebraicComplex 4) : Prop :=
  ∃i : Fin 6,O.middleCoeff M i=0 ∧ O.middleCoeff M (5-i)=0

private theorem mask_split : ∀B : Fin 6→Bool,
    (Finset.univ.filter fun i=>B i).card≤4 →
      (Finset.univ.filter fun i=>B i).card≤2 ∨
      (∃j : Fin 4,∃bit : Bool,∀i,B i=true → O.middleWord i j=bit) ∨
      N.MaskCondition B ∨ (∃i,B i=false ∧ B (5-i)=false) := by decide

theorem fixed_of_mask (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (j : Fin 4) (bit : Bool) (h : ∀i,N.mask M i=true → O.middleWord i j=bit) :
    T.FixedPort M j bit := by
  intro x hx
  have hw : weight x=2 := by by_contra hn; exact hx (he x hn)
  obtain ⟨i,hi⟩ := middle_surj x hw
  rw [←hi]
  apply h i
  classical
  simpa only [N.mask,decide_eq_true_eq,O.middleCoeff,hi] using hx

theorem sparse_dispatch (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (hs : (T.support M).card≤4) : EOTract {⟨4,M⟩} ∨ N.Applicable M ∨ Plane M := by
  classical
  rw [support_card M he] at hs
  rcases mask_split (N.mask M) hs with hh|hh|hh|hh
  · left
    apply T.small_tract M he
    simpa only [support_card M he,middleSupport] using hh
  · obtain ⟨j,bit,h⟩ := hh
    exact Or.inl (T.fixed_tract M he j bit (fixed_of_mask M he j bit h))
  · exact Or.inr (Or.inl hh)
  · right; right
    simpa only [Plane,N.mask,decide_eq_false_iff_not,not_not,O.middleCoeff] using hh

/-- Both support-only outcomes are discharged; no assumed hardness endpoint is
introduced. Only the explicit binary-plane case remains outside this theorem. -/
theorem outside_plane (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (hs : (T.support M).card≤4) (hp : ¬Plane M) : EOTract {⟨4,M⟩} ∨ N.Applicable M := by
  rcases sparse_dispatch M he hs with h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hp h)

namespace Oracle
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end Oracle

def complex (M : Signature AlgebraicComplex 4) : Signature ℂ 4 := fun x=>(M x : ℂ)
theorem complex_algebraic (M : Signature AlgebraicComplex 4) : ∀x,IsAlgebraic ℚ (complex M x) :=
  fun x=>(M x).property.isAlgebraic

theorem complex_eo (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M) :
    DenseEOUnitLocal.EOSupport (complex M) := by
  intro x hx
  simp only [complex,he x hx,ZeroMemClass.coe_zero]

theorem complex_mask (M : Signature AlgebraicComplex 4) : N.mask (complex M)=N.mask M := by
  classical
  funext i
  simp [N.mask,O.middleCoeff,complex]

theorem complex_applicable (M : Signature AlgebraicComplex 4) (h : N.Applicable M) :
    N.Applicable (complex M) := by
  unfold N.Applicable
  rw [complex_mask]
  exact h

local instance complexOriginalAlgebra (M : Signature AlgebraicComplex 4) :
    Algebra ℚ (Oracle.field (complex M)) := (Oracle.field (complex M)).algebra'

/-- An actual classification outside the stated affine-plane residual: the hard
branch is the constructed original-signature/native-X counting reduction. -/
theorem outside_plane_hard_or_tract (M : Signature AlgebraicComplex 4)
    (he : DenseEOUnitLocal.EOSupport M) (hs : (T.support M).card≤4) (hp : ¬Plane M) :
    EOTract {⟨4,M⟩} ∨ Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      Oracle.targetEncoding (Oracle.presentation (complex M) (complex_algebraic M)).encoding
      (Oracle.targetValue (complex M) (complex_algebraic M)) := by
  rcases outside_plane M he hs hp with h|h
  · exact Or.inl h
  · exact Or.inr (EOQuaternarySparseFourSource.witnessCountingHard (complex M)
      (complex_algebraic M) (complex_eo M he) (complex_applicable M h))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseDispatch
