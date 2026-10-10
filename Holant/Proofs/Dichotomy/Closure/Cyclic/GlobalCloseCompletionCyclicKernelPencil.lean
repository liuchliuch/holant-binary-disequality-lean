import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicKernelCross
import Holant.ReedMuller.CoefficientAtlas.Physical

/-! Exact Walsh transport for an arbitrary I/X pencil, followed by its
literal RM-support repeated-word values. The original kernel coefficients
and every factor of two remain explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicKernelPencil
open Holant Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
namespace C
export GlobalCloseCompletionCyclicKernelCross (parity)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false

def pencil (a b : ℂ) : Kernel ℂ := fun u v=>a*Signature.equality u v+b*Signature.disequality u v

def diagonal (a b : ℂ) : Kernel ℂ :=
  fun u v=>if u=v then 2*(if u then a-b else a+b) else 0

def weightedCard (q : Signature ℂ 8) (p : Fin 28) (a b : ℂ) : Signature ℂ 6 :=
  fun y=>2*((a+b)*q (fill p false y)+(a-b)*q (fill p true y))

theorem pullback (a b : ℂ) : Kernel.pullback (pencil a b) walshKernel=diagonal a b := by
  funext u v
  cases u <;> cases v <;>
    norm_num [Kernel.pullback,Kernel.mul,Kernel.transpose,pencil,diagonal,walshKernel,
      Signature.equality,Signature.disequality] <;> ring

theorem weighted_eq_contract (q : Signature ℂ 8) (p : Fin 28) (a b : ℂ) :
    weightedCard q p a b=Signature.contract (diagonal a b) (Tensor.reindex (ports p).symm q) := by
  funext y
  simp only [weightedCard,fill_eq_cons,Signature.contract,Fintype.sum_bool,diagonal,
    Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,zero_mul,zero_add,add_zero,Tensor.reindex]
  ring

theorem walsh_physical_pencil (f : Signature ℂ 8) (p : Fin 28) (a b : ℂ) :
    walsh (Signature.contract (pencil a b) (Tensor.reindex (ports p).symm f))=
      weightedCard (walsh f) p a b := by
  have h : Signature.contract (pencil a b) (Tensor.reindex (ports p).symm f)=
      Signature.coordinateAction (fun _=>walshKernel) (weightedCard (walsh f) p a b) := by
    conv_lhs => rw [←physical_of_walsh f]
    rw [←coordinateAction_reindex,coordinateAction_contract,pullback,←weighted_eq_contract]
  rw [h,walsh_of_physical]

theorem zero_pair_lift : ∀t : Fin 3→Bool,
    fill 0 (C.parity t) (repeatedWord t)=word (lift 0 t) ∧
      ∀a : Param,fill 0 (!(C.parity t)) (repeatedWord t)≠word a := by decide

theorem weighted_repeated {q : Signature ℂ 8} (support : SupportRM q)
    (a b : ℂ) (t : Fin 3→Bool) :
    weightedCard q 0 a b (repeatedWord t)=
      (if C.parity t then a-b else a+b)*plusCard q 0 (repeatedWord t) := by
  have active := (zero_pair_lift t).1
  have zero : q (fill 0 (!(C.parity t)) (repeatedWord t))=0 :=
    outside_zero support _ (zero_pair_lift t).2
  rw [plusCard_repeated support]
  cases hp : C.parity t
  · simp only [hp,Bool.not_false] at active zero
    simp only [weightedCard,active,zero,mul_zero,add_zero,Bool.false_eq_true,ite_false]
    ring
  · simp only [hp,Bool.not_true] at active zero
    simp only [weightedCard,active,zero,mul_zero,zero_add,ite_true]
    ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicKernelPencil
end
