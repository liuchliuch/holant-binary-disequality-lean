import Holant.Certificates.IcosahedralSeparator.Provenance
import Holant.Certificates.IcosahedralSeparator.UniformOutputCode
import Holant.Certificates.OppositeIcosahedral.SourceInterface

/-! Direct fixed-I covariance. The original six-port tensor stays on the
left of the contraction; only its analytical dictionary is used in hypotheses. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
namespace Opposite
open Holant.Certificates.OppositeIcosahedral

def firstKernel : Matrix Bool Bool ℂ := kappa uniformKernel
def secondKernel : Matrix Bool Bool ℂ := kappa subsequentKernel
def output (i : Fin 30) : FourTensor := transport (uniformOutput i)
def finalOutput (i : Fin 30) : Matrix Bool Bool ℂ :=
  fun a b => Signature.contract secondKernel (output i) ![a,b]

theorem contract_transport {n : ℕ} (f : Signature ℂ (n+2)) (K : Matrix Bool Bool ℂ) :
    Signature.contract (kappa K) (transport f) = transport (Signature.contract K f) := by
  have hh := card_covariance (Equiv.refl _) (transport f) K
  simpa only [card,Tensor.reindex_refl,analytical_transport] using hh

theorem original_first (h : Signature ℂ 6) (i : Fin 30)
    (hi : Signature.contract uniformKernel (analytical h) = uniformOutput i) :
    Signature.contract firstKernel h = output i := by
  have hh := card_covariance (Equiv.refl _) h uniformKernel
  simpa only [card,Tensor.reindex_refl,hi,firstKernel,output] using hh

theorem original_second (h : Signature ℂ 6) (i : Fin 30)
    (hi : Signature.contract uniformKernel (analytical h) = uniformOutput i) :
    (fun a b => Signature.contract secondKernel (Signature.contract firstKernel h) ![a,b]) = finalOutput i := by
  rw [original_first h i hi]
  rfl

theorem transport_binary (f : Signature ℂ 2) (a b : Bool) :
    transport f ![a,b] = binaryTransport (fun c d => f ![c,d]) a b := by
  rw [transport_eq_tensor]
  cases a <;> cases b <;>
    simp [transportTensor,OppositeIcosahedral.weight,Fin.prod_univ_succ,binaryTransport,D_weight,
      Matrix.mul_apply,Signature.equality]
  <;> ring

theorem finalOutput_eq (i : Fin 30) : finalOutput i = binaryTransport (subsequentOutput i) := by
  ext a b
  change Signature.contract (kappa subsequentKernel) (transport (uniformOutput i)) ![a,b] = _
  rw [contract_transport,transport_binary]
  rfl

def pairWeight (p : Bool × Bool) : ℂ := diagonalWeight p.1*diagonalWeight p.2

theorem pairWeight_ne_zero (p : Bool × Bool) : pairWeight p ≠ 0 :=
  mul_ne_zero (diagonalWeight_ne_zero _) (diagonalWeight_ne_zero _)

theorem flatten_transport (r : Fin 3) (f : FourTensor) :
    flatten r (transport f) = Matrix.diagonal pairWeight * flatten r f * Matrix.diagonal pairWeight := by
  rw [transport_eq_tensor]
  fin_cases r <;> ext a b <;>
    simp [flatten,flatten0,flatten1,flatten2,transportTensor,OppositeIcosahedral.weight,Fin.prod_univ_succ,
      Matrix.diagonal_mul,Matrix.mul_diagonal,pairWeight] <;> ring

theorem flatten_rank (r : Fin 3) (f : FourTensor) :
    (flatten r (transport f)).rank = (flatten r f).rank := by
  rw [flatten_transport,Matrix.rank_mul_eq_left_of_det_ne_zero,Matrix.rank_mul_eq_right_of_det_ne_zero]
  · simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun p _ => pairWeight_ne_zero p)
  · simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun p _ => pairWeight_ne_zero p)

theorem final_nonsingular_iff (i : Fin 30) :
    (finalOutput i).det ≠ 0 ↔ Matrix.det (Matrix.of (subsequentOutput i)) ≠ 0 := by
  rw [finalOutput_eq]
  exact binary_nonsingular_iff (Matrix.of (subsequentOutput i))

theorem final_outside_iff (i : Fin 30) :
    ¬Direction (finalOutput i * OppositeIcosahedral.X) ↔
      ¬groupDirection .icosahedral (Matrix.of (subsequentOutput i) * OppositeIcosahedral.X) := by
  rw [finalOutput_eq]
  exact outside_transfer_iff (Matrix.of (subsequentOutput i))

end Opposite
end
end Holant.Certificates.IcosahedralSeparator
