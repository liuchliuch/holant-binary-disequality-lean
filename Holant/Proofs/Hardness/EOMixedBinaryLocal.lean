import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! A literal binary row breaks affine phases without destroying a full
nonproduct plane. Unequal fourth powers suffice, including finite-order
phase ratios. The row weights below are the exact native-X orientation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOMixedBinaryLocal
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export EOBinaryPlaneCore (lift compress word)
end C
namespace P
export EOBinaryPlaneClassification (Full Cross CommonFourth full_product_iff full_affine_iff)
end P
set_option backward.isDefEq.respectTransparency false

variable (f : Signature AlgebraicComplex 2) (p q : AlgebraicComplex)

def weighted : Signature AlgebraicComplex 2 := fun x=>(if x 0 then p else q)*f x

theorem weighted_full (hf : P.Full f) (hp : p≠0) (hq : q≠0) : P.Full (weighted f p q) := by
  intro x
  apply mul_ne_zero
  · cases x 0 <;> assumption
  · exact hf x

theorem weighted_cross_iff (hp : p≠0) (hq : q≠0) :
    P.Cross (weighted f p q) ↔ P.Cross f := by
  change (q*f ![false,false])*(p*f ![true,true])=
    (q*f ![false,true])*(p*f ![true,false]) ↔ _
  have hl : (q*f ![false,false])*(p*f ![true,true])=
      (p*q)*(f ![false,false]*f ![true,true]) := by ring
  have hr : (q*f ![false,true])*(p*f ![true,false])=
      (p*q)*(f ![false,true]*f ![true,false]) := by ring
  rw [hl,hr]
  exact ⟨fun h=>mul_left_cancel₀ (mul_ne_zero hp hq) h,fun h=>congrArg (fun z=>(p*q)*z) h⟩

theorem weighted_not_product (hf : P.Full f) (hn : ¬Product f) (hp : p≠0) (hq : q≠0) :
    ¬Product (weighted f p q) := by
  rw [P.full_product_iff _ (weighted_full f p q hf hp hq),weighted_cross_iff f p q hp hq]
  exact fun h=>hn ((P.full_product_iff f hf).mpr h)

theorem weighted_not_affine (hf : P.Full f) (ha : Affine f) (hp : p≠0) (hq : q≠0)
    (hne : p^4≠q^4) : ¬Affine (weighted f p q) := by
  intro h
  have hc := ((P.full_affine_iff _ (weighted_full f p q hf hp hq)).mp h).1 ![true,false]
  change (p*f ![true,false])^4=(q*f ![false,false])^4 at hc
  rw [mul_pow,mul_pow,((P.full_affine_iff f hf).mp ha).1 ![true,false]] at hc
  exact hne (mul_right_cancel₀ (pow_ne_zero 4 (hf ![false,false])) hc)

theorem weighted_not_tract (hf : P.Full f) (ha : Affine f) (hn : ¬Product f)
    (hp : p≠0) (hq : q≠0) (hne : p^4≠q^4) :
    ¬EOTract {⟨4,C.lift (weighted f p q)⟩} := by
  rw [EOBinaryPlaneTract.lift_tract_iff]
  exact not_or.mpr ⟨weighted_not_affine f p q hf ha hp hq hne,
    weighted_not_product f p q hf hn hp hq⟩

/-- The original binary has p at 01 and q at 10. -/
def anti : Signature AlgebraicComplex 2 :=
  fun x=>if x 0 then (if x 1 then 0 else q) else (if x 1 then p else 0)

theorem anti_product : Product (anti p q) :=
  EOQuaternarySparseTract.binary_of_shape _ (Or.inr (Or.inl ⟨rfl,rfl⟩))

theorem anti_central : Signature.CentralSupport (anti p q) := by
  intro x hx
  have he : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [he]
  cases h0 : x 0 <;> cases h1 : x 1
  · rfl
  · exfalso; apply hx; rw [he,h0,h1]; decide
  · exfalso; apply hx; rw [he,h0,h1]; decide
  · rfl

theorem anti_tract : EOTract {⟨2,anti p q⟩} := by
  refine ⟨by simp,?_,.positive,.product,?_,?_⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨⟨1,rfl⟩,anti_central p q⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    intro a b c ha hb hc
    exact Or.inl (product_support_xor3 (anti_product p q) a b c ha hb hc)
  · intro g hg e
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact EOBinaryPlaneTract.product_signed e.ports.symm (anti_product p q)

/-- Arbitrary finite original port orders are analytical only. -/
theorem compressed_affine (M : Signature AlgebraicComplex 4) (e : Equiv.Perm (Fin 4))
    (ha : Affine M) : Affine (C.compress (Tensor.reindex e M)) := by
  have h := ha.precompose (fun x j=>x (e j)) (coordinates_isAffineMap e)
  change Affine (Tensor.reindex e M) at h
  have hh := h.precompose EOBinaryPlaneCore.pairing.word
    (EOBinaryPlaneTract.pairing_affine EOBinaryPlaneCore.pairing)
  change Affine (fun x : Fin 2→Bool=>Tensor.reindex e M (EOBinaryPlaneCore.pairing.word x)) at hh
  change Affine (fun x : Fin 2→Bool=>Tensor.reindex e M (C.word x))
  simpa only [EOBinaryPlaneCore.pairing_word] using hh

theorem compressed_not_product (M : Signature AlgebraicComplex 4) (e : Equiv.Perm (Fin 4))
    (hplane : C.lift (C.compress (Tensor.reindex e M))=Tensor.reindex e M)
    (hn : ¬Product M) : ¬Product (C.compress (Tensor.reindex e M)) := by
  intro h
  have hh := EOBinaryPlaneTract.product_lift h
  rw [hplane] at hh
  exact hn (EOBinaryPlaneTract.product_unreindex e M hh)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOMixedBinaryLocal
