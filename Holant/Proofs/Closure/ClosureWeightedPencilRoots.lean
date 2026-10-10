import Holant.Proofs.Closure.ClosureWeightedPencilRawClassification

/-! Actual inverse port weights are roots of order twice the marked phase
order. Their exact tensor transport therefore preserves that enlarged analytic
ratio condition. This states no availability of extra physical phase kernels.
New proof, awaiting strict kernel validation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain ClosureRootPencil

theorem root_double {m : ℕ} {B : Kernel ℂ} (rooted : IsRootMonomial m B) :
    IsRootMonomial (2*m) B := by
  have double (z : ℂ) (h : z^m=1) : z^(2*m)=1 := by
    rw [Nat.mul_comm 2 m,pow_mul,h,one_pow]
  rcases rooted with ⟨h01,h10,h00,h11,ratio⟩ | ⟨h00,h11,h01,h10,ratio⟩
  · exact Or.inl ⟨h01,h10,h00,h11,double _ ratio⟩
  · exact Or.inr ⟨h00,h11,h01,h10,double _ ratio⟩

theorem Anchor.weights_double_root {m : ℕ} {d : Scalar} {U V : Signature Scalar 4}
    (A : Anchor m d U V) (square : Roots m (d^2)) :
    ∀ i,complexWeights A.weights i^(2*m)=1 := by
  intro i
  have hd : (d : ℂ)^(2*m)=1 := by
    have scalar : d^(2*m)=1 := by
      rw [pow_mul]
      exact square
    exact_mod_cast scalar
  cases side : (A.presentation.ports.symm i).2 <;>
    simp [complexWeights,Anchor.weights,ClosureShiftedWeighted.rightWeights,side,hd]

theorem portBinary_root {k : ℕ} (r : Fin 4 → ℂ) (nonzero : ∀ i,r i≠0)
    (roots : ∀ i,r i^k=1) (ports : (Fin 2 × Bool) ≃ Fin 4) (e : Fin 2)
    (B : Kernel ℂ) (rooted : IsRootMonomial k B) :
    IsRootMonomial k (portBinary r ports e B) := by
  let u := r (ports (e,false))
  let v := r (ports (e,true))
  have hu : u≠0 := nonzero _
  have hv : v≠0 := nonzero _
  have ur : u^k=1 := roots _
  have vr : v^k=1 := roots _
  rcases rooted with ⟨h01,h10,h00,h11,ratio⟩ | ⟨h00,h11,h01,h10,ratio⟩
  · left
    refine ⟨by simp [portBinary,h01],by simp [portBinary,h10],?_,?_,?_⟩
    · simpa only [portBinary,WeightedGauge.bitWeight_false,one_mul,mul_one] using h00
    · simpa only [portBinary,WeightedGauge.bitWeight_true] using mul_ne_zero (mul_ne_zero hu h11) hv
    · simp only [portBinary,WeightedGauge.bitWeight_true,WeightedGauge.bitWeight_false,one_mul,mul_one]
      change ((u*B true true*v)/B false false)^k=1
      have expression : (u*B true true*v)/B false false=u*(B true true/B false false)*v := by
        ring
      rw [expression,mul_pow,mul_pow,ur,ratio,vr]
      norm_num
  · right
    refine ⟨by simp [portBinary,h00],by simp [portBinary,h11],?_,?_,?_⟩
    · simpa only [portBinary,WeightedGauge.bitWeight_false,WeightedGauge.bitWeight_true,one_mul] using mul_ne_zero h01 hv
    · simpa only [portBinary,WeightedGauge.bitWeight_false,WeightedGauge.bitWeight_true,mul_one] using mul_ne_zero hu h10
    · simp only [portBinary,WeightedGauge.bitWeight_true,WeightedGauge.bitWeight_false,one_mul,mul_one]
      change ((u*B true false)/(B false true*v))^k=1
      have expression : (u*B true false)/(B false true*v)=u*(B true false/B false true)/v := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      rw [expression,div_pow,mul_pow,ur,ratio,vr]
      norm_num

theorem complementary_inverse_fixed_root {m : ℕ} (r : Fin 4 → Scalar)
    (nonzero : ∀ i,r i≠0) (roots : ∀ i,complexWeights r i^(2*m)=1)
    (U V : Signature Scalar 4)
    (C : ClosureRootPencil.Complementary m
      (complexTensor (WeightedGauge.gauge r U)) (complexTensor (WeightedGauge.gauge r V))) :
    IsRootMonomial (2*m) (complementaryInverse r nonzero U V C).fixed := by
  apply portBinary_root (fun i => (complexWeights r i)⁻¹)
    (fun i => inv_ne_zero (complexWeights_nonzero r nonzero i))
    (fun i => by rw [inv_pow,roots i,inv_one])
  exact root_double C.ruling.fixedRoot

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
