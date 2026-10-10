import Holant.ReedMuller.CoefficientAtlas.ContractionTransport

/-! Ordered, nonuniform coefficient transport. These are analytic identities;
no coefficient similarity is declared to be an available gadget. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant
open Holant.ReedMuller.CoefficientAtlas
variable {K : Type*} [CommSemiring K]
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

theorem action_head {n : ℕ} (L : Fin (n+1) → Kernel K) (f : Signature K (n+1))
    (a : Bool) (x : Fin n → Bool) :
    Signature.coordinateAction L f (Fin.cons a x) = ∑ b : Bool,
      L 0 a b*Signature.coordinateAction (fun j => L j.succ) (Signature.pin f b) x := by
  simp [Signature.coordinateAction,sum_words_succ,Fin.prod_univ_succ,Signature.pin,
    Finset.mul_sum,mul_assoc]

def pairKernel (A B E : Kernel K) : Kernel K := Kernel.mul (Kernel.transpose A) (Kernel.mul E B)

theorem contract_action {n : ℕ} (L : Fin (n+2) → Kernel K) (E : Kernel K)
    (f : Signature K (n+2)) :
    Signature.contract E (Signature.coordinateAction L f) =
      Signature.coordinateAction (fun j => L j.succ.succ)
        (Signature.contract (pairKernel (L 0) (L 1) E) f) := by
  funext x
  simp only [Signature.contract,action_head]
  dsimp only [Signature.coordinateAction,Signature.pin,Signature.contract,pairKernel,Kernel.mul,Kernel.transpose]
  simp only [Fintype.sum_bool,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Fin.succ_zero_eq_one]
  ring

theorem reindex_action {n : ℕ} (L : Fin n → Kernel K) (e : Equiv.Perm (Fin n))
    (f : Signature K n) :
    Tensor.reindex e (Signature.coordinateAction L f) =
      Signature.coordinateAction (fun j => L (e.symm j)) (Tensor.reindex e f) := by
  funext x
  simp only [Signature.coordinateAction,Tensor.reindex]
  rw [← (assignmentEquiv e).sum_comp
    (fun y => (∏ j, L j (x (e j)) (y j))*f y)]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  simpa only [assignmentEquiv,Equiv.coe_fn_mk,Equiv.symm_apply_apply] using
    (Equiv.prod_comp e (fun j => L (e.symm j) (x j) (y j)))

end Holant.Certificates.OctahedralSeparator
