import Holant.Proofs.Hardness.AntiselfdualNormalize
import Holant.Proofs.Hardness.RealDenseCapClassification

/-! A literal two-original-M sign twist from any antisymmetric cap. The input
signature need not be antiselfdual. Cap boundary 1 meets original port 0 of the
second M through native X; cap boundary 0 becomes output 0. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSignTwist
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export GeneralCancellationCapPin (network full_table antiTensor coefficients oriented)
end C
namespace N
export AntiselfdualNormalize (normalized capNetwork contraction template valid template_actual)
end N
variable {K : Type*} [Field K]

/-- Literal cap coefficients, with no supplied gadget or normalization proof. -/
def AntisymmetricCap (M : Signature K 4) (k : Fin 6) (p : K) : Prop :=
  (C.coefficients M k).1=p ∧ (C.coefficients M k).2= -p

theorem denote (M : Signature K 4) (he : EvenSupport M) (k : Fin 6) (p : K)
    (h : AntisymmetricCap M k p) :
    (N.capNetwork M k).denote=p • N.normalized M := by
  funext x
  rw [N.contraction,C.full_table M he]
  have hx : ![x 0,x 1,x 2,x 3]=x := by funext i; fin_cases i <;> rfl
  have hp : (C.oriented M (k,false)).1=p := h.1
  have hq : (C.oriented M (k,false)).2= -p := h.2
  rw [hp,hq]
  cases h0 : x 0 <;>
    simp [C.antiTensor,N.normalized,h0,Pi.smul_apply,smul_eq_mul]
  · have he : ![false,x 1,x 2,x 3]=x := by simpa only [h0] using hx
    simp only [he,eq_self,true_or]
  · have he : ![true,x 1,x 2,x 3]=x := by simpa only [h0] using hx
    simp only [he,eq_self,true_or]

theorem template_denote (M : Signature K 4) (he : EvenSupport M)
    (k : Fin 6) (p : K) (h : AntisymmetricCap M k p) :
    ((N.template M k).network (N.valid M k) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=p • N.normalized M := by
  rw [N.template_actual]
  exact denote M he k p h

theorem counts (M : Signature K 4) (k : Fin 6) :
    (N.template M k).vertices.length=2 ∧ (N.template M k).edges.length=2 := by
  fin_cases k <;> exact ⟨rfl,rfl⟩

theorem normalized_eo (M : Signature K 4) (h : DenseEOUnitLocal.EOSupport M) :
    DenseEOUnitLocal.EOSupport (N.normalized M) := by
  intro x hx
  simp [N.normalized,h x hx]

theorem normalized_middle (M : Signature K 4) (h : DenseEOUnitLocal.NonzeroMiddle M) :
    DenseEOUnitLocal.NonzeroMiddle (N.normalized M) := by
  simpa [DenseEOUnitLocal.NonzeroMiddle,entries,N.normalized] using h

/-- The canonical exceptional plane, in original b,c,d,w,z,y order. -/
structure Exceptional (M : Signature ℝ 4) : Prop where
  cd : (entries M).c=(entries M).d
  cw : (entries M).c=(entries M).w
  cz : (entries M).c=(entries M).z
  total : (entries M).b+(entries M).y= -2*(entries M).c
  asymmetric : (entries M).b≠(entries M).y

def exceptionalScale (M : Signature ℝ 4) : ℝ := (entries M).b+(entries M).c

theorem exceptional_scale_nonzero (M : Signature ℝ 4) (h : Exceptional M) :
    exceptionalScale M≠0 := by
  intro hz
  apply h.asymmetric
  dsimp [exceptionalScale] at hz
  linarith [h.total]

theorem exceptional_cap (M : Signature ℝ 4) (h : Exceptional M) :
    AntisymmetricCap M 3 (exceptionalScale M) := by
  constructor
  · rfl
  · change (entries M).z+(entries M).y= -((entries M).b+(entries M).c)
    rw [←h.cz]
    linarith [h.total]

theorem exceptional_cap2 (M : Signature ℝ 4) (h : Exceptional M) :
    C.coefficients (N.normalized M) 2=
      ((entries M).b-(entries M).c,(entries M).b+3*(entries M).c) := by
  simp only [C.coefficients,Matrix.cons_val_two]
  change ((entries M).b + -(entries M).z,(entries M).c + -(entries M).y)=_
  ext
  · rw [←h.cz]; ring
  · dsimp; linarith [h.total]

theorem exceptional_imbalance (M : Signature ℝ 4) (h : Exceptional M)
    (hc : (entries M).c≠0) :
    (C.coefficients (N.normalized M) 2).1^2≠
      (C.coefficients (N.normalized M) 2).2^2 := by
  rw [exceptional_cap2 M h]
  dsimp only
  have hp := exceptional_scale_nonzero M h
  have hn : (-8 : ℝ)*(entries M).c*exceptionalScale M≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hc) hp
  intro he
  apply hn
  dsimp [exceptionalScale]
  nlinarith [he]

/-- Either existing cap source is now available, derived from literal entries. -/
theorem exceptional_access (M : Signature ℝ 4) (h : Exceptional M)
    (hc : (entries M).c≠0) :
    GeneralCancellationCapPin.Applicable (N.normalized M) ∨
      GeneralGeometricCapLocal.Applicable (N.normalized M) := by
  by_contra hn
  push Not at hn
  exact exceptional_imbalance M h hc
    (RealDenseCapClassification.no_access_balanced _ hn.1 hn.2 2)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSignTwist
