import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SixPortProblem
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2CurrentComplement

/-! Literal semantic bridge for the finite C2 table: every one of the thirty
cards is exactly an original ordered I/X contraction, with all residual words
and scalars preserved. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortCoordinates
open Holant Holant.Tractable
open Holant.Pauli.ExoticKlein.SixPort
open IntegerCertificate LinearCertificate
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open GlobalCloseCompletionC2SixPortProblem
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option Elab.async false

def orderTable : Fin 30 → Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,2,1,3,4,5],![0,2,1,3,4,5],![0,3,1,2,4,5],![0,3,1,2,4,5],![0,4,1,2,3,5],![0,4,1,2,3,5],![0,5,1,2,3,4],![0,5,1,2,3,4],![1,2,0,3,4,5],![1,2,0,3,4,5],![1,3,0,2,4,5],![1,3,0,2,4,5],![1,4,0,2,3,5],![1,4,0,2,3,5],![1,5,0,2,3,4],![1,5,0,2,3,4],![2,3,0,1,4,5],![2,3,0,1,4,5],![2,4,0,1,3,5],![2,4,0,1,3,5],![2,5,0,1,3,4],![2,5,0,1,3,4],![3,4,0,1,2,5],![3,4,0,1,2,5],![3,5,0,1,2,4],![3,5,0,1,2,4],![4,5,0,1,2,3],![4,5,0,1,2,3]]

def inverseTable : Fin 30 → Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,2,1,3,4,5],![0,2,1,3,4,5],![0,2,3,1,4,5],![0,2,3,1,4,5],![0,2,3,4,1,5],![0,2,3,4,1,5],![0,2,3,4,5,1],![0,2,3,4,5,1],![2,0,1,3,4,5],![2,0,1,3,4,5],![2,0,3,1,4,5],![2,0,3,1,4,5],![2,0,3,4,1,5],![2,0,3,4,1,5],![2,0,3,4,5,1],![2,0,3,4,5,1],![2,3,0,1,4,5],![2,3,0,1,4,5],![2,3,0,4,1,5],![2,3,0,4,1,5],![2,3,0,4,5,1],![2,3,0,4,5,1],![2,3,4,0,1,5],![2,3,4,0,1,5],![2,3,4,0,5,1],![2,3,4,0,5,1],![2,3,4,5,0,1],![2,3,4,5,0,1]]

def order (c : Fin 30) : Equiv.Perm (Fin 6) where
  toFun := orderTable c
  invFun := inverseTable c
  left_inv := by
    have all : ∀ (c : Fin 30) (i : Fin 6), inverseTable c (orderTable c i) = i := by decide +kernel
    exact all c
  right_inv := by
    have all : ∀ (c : Fin 30) (i : Fin 6), orderTable c (inverseTable c i) = i := by decide +kernel
    exact all c

def phase : Fin 30 → Bool := ![false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]

def unpack (c : Fin 30) (w : Fin 16) (b : Bool) : Fin 6 → Bool :=
  fun i => (Fin.cons b (Fin.cons (b ^^ phase c) ((wordEquiv 4).symm w)) : Fin 6 → Bool) ((order c).symm i)

theorem input_table_correct : ∀ (c : Fin 30) (w : Fin 16) (b : Bool),
    inputTable c ⟨2*w.val+(if b then 1 else 0),by cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega⟩ = wordEquiv 6 (unpack c w b) := by
  decide +kernel

def coefficients (f : Signature ℂ 6) : Fin 64 → ℂ := fun w => f ((wordEquiv 6).symm w)

private theorem evaluate_add (u v : LinearCertificate.Row 64) (s : Fin 64 → ℂ) :
    evaluate (u+v) s = evaluate u s + evaluate v s := by
  simp [evaluate,Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]

theorem card_coefficients (f : Signature ℂ 6) (c : Fin 30) (w : Fin 16) :
    evaluate (IntegerCertificate.mapRow (GlobalCloseCompletionC2SixPortProblem.card c w)) (coefficients f) =
      f (unpack c w false) + f (unpack c w true) := by
  have hc : IntegerCertificate.mapRow (GlobalCloseCompletionC2SixPortProblem.card c w) =
      LinearCertificate.unitRow (inputTable c ⟨2*w.val,by omega⟩) +
      LinearCertificate.unitRow (inputTable c ⟨2*w.val+1,by omega⟩) := by
    funext i
    simp [IntegerCertificate.mapRow,GlobalCloseCompletionC2SixPortProblem.card,LinearCertificate.unitRow]
  rw [hc,evaluate_add,evaluate_unitRow,evaluate_unitRow]
  have h0 := input_table_correct c w false
  have h1 := input_table_correct c w true
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero,ite_true] at h0 h1
  simp only [coefficients,h0,h1,Equiv.symm_apply_apply]

theorem card_contract (f : Signature ℂ 6) (c : Fin 30) (w : Fin 16) :
    evaluate (IntegerCertificate.mapRow (GlobalCloseCompletionC2SixPortProblem.card c w)) (coefficients f) =
      Signature.contract (originalC2Binary (phase c)) (Tensor.reindex (order c).symm f)
        ((wordEquiv 4).symm w) := by
  rw [card_coefficients]
  unfold unpack
  cases hp : phase c <;>
    simp [Signature.contract,Tensor.reindex,originalC2Binary,
      Holant.Certificates.MatchingContractionClosure.X,Matrix.one_apply,
      Signature.disequality]
  all_goals exact add_comm _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortCoordinates
end
