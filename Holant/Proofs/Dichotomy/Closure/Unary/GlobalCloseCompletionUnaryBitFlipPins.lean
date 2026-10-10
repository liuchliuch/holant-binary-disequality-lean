import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBitFlip

/-! Exact semantic transport through chosen-sign caps, port reindexing and
ordinary equality loops whose two mask bits agree. No coordinate flip is
introduced as a physical resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBitFlipPins
open Holant
namespace F
export GlobalCloseCompletionUnaryBitFlip (word value tensorClosure_iff)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n m : ℕ}

def cap (i : Fin n) (b : Bool) (f : Signature K n) : Signature K n :=
  fun x=>f (Function.update x i b)

theorem word_update (mask x : Fin n→Bool) (i : Fin n) (b : Bool) :
    F.word mask (Function.update x i b)=Function.update (F.word mask x) i (b^^mask i) := by
  funext j
  by_cases same : j=i
  · subst j;simp [F.word]
  · simp [F.word,same]

theorem cap_flip (mask : Fin n→Bool) (f : Signature K n) (i : Fin n) (b : Bool) :
    cap i b (F.value mask f)=F.value mask (cap i (b^^mask i) f) := by
  funext x
  change f (F.word mask (Function.update x i b))=f (Function.update (F.word mask x) i (b^^mask i))
  rw [word_update]

theorem cap_small_iff (mask : Fin n→Bool) (f : Signature K n) (i : Fin n) (b : Bool) :
    Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) (cap i b (F.value mask f)) ↔
      Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) (cap i (b^^mask i) f) := by
  rw [cap_flip,F.tensorClosure_iff]

theorem reindex_flip (e : Fin n≃Fin m) (mask : Fin n→Bool) (f : Signature K n) :
    Tensor.reindex e (F.value mask f)=F.value (fun i=>mask (e.symm i)) (Tensor.reindex e f) := by
  funext x
  change f (fun i=>x (e i)^^mask i)=f (fun i=>x (e i)^^mask (e.symm (e i)))
  simp only [Equiv.symm_apply_apply]

theorem word_cons (mask x : Fin n→Bool) (a b : Bool) :
    F.word (Fin.cons b mask) (Fin.cons a x)=Fin.cons (a^^b) (F.word mask x) := by
  funext i
  refine Fin.cases rfl (fun _=>rfl) i

theorem contract_equal_mask (mask : Fin n→Bool) (b : Bool) (f : Signature K (n+2)) :
    Signature.contract Signature.equality (F.value (Fin.cons b (Fin.cons b mask)) f)=
      F.value mask (Signature.contract Signature.equality f) := by
  funext x
  simp only [Signature.contract_equality,F.value,word_cons]
  cases b <;> simp [add_comm]

def project (i : Fin (n+1)) (b : Bool) (f : Signature K (n+1)) : Signature K n :=
  fun x=>Tensor.reindex (Equiv.swap 0 i) f (Fin.cons b x)

theorem front_flip (mask : Fin (n+1)→Bool) (f : Signature K (n+1)) (b : Bool) :
    (fun x=>F.value mask f (Fin.cons b x))=
      F.value (fun j=>mask j.succ) (fun x=>f (Fin.cons (b^^mask 0) x)) := by
  funext x
  change f (F.word mask (Fin.cons b x))=f (Fin.cons (b^^mask 0) (F.word (fun j=>mask j.succ) x))
  congr 1
  funext j
  refine Fin.cases rfl (fun _=>rfl) j

theorem project_flip (mask : Fin (n+1)→Bool) (f : Signature K (n+1))
    (i : Fin (n+1)) (b : Bool) :
    project i b (F.value mask f)=
      F.value (fun j=>mask (Equiv.swap 0 i j.succ)) (project i (b^^mask i) f) := by
  unfold project
  rw [reindex_flip,front_flip]
  simp only [Equiv.symm_swap,Equiv.swap_apply_left]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBitFlipPins
end
