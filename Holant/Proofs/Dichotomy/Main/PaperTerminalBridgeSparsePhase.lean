import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseSign
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsAnchor

/-! Attach only genuinely available native antidiagonals. The exact two
projective multipliers are retained by the realization, and nonzero phases
preserve endpoint support. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparsePhase
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace A
export PaperTerminalBridgeAntiGroup (Available)
end A
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace S
export PaperTerminalBridgeComplementSign (Complement)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def phase (f : Signature K 4) (t : K) (i : Fin 4) : Signature K 4 :=
  fun x=>(if x i then t else 1)*f x

theorem actual (F : SignatureFamily K) (f : Signature K 4)
    (hf : Gadget.RealizesUpTo F .disequality f) (t : K) (ht : A.Available F t) (i : Fin 4) :
    Gadget.RealizesUpTo F .disequality (phase f t i) := by
  obtain ⟨c,hc,hf⟩:=hf
  obtain ⟨d,hd,ht⟩:=ht
  have out:=realizes_splice F (fun x=>c*f x) (fun x=>d*C.antiTensor 1 t x) hf ht i
  rw [PaperTerminalBridgeEqualProductsAnchor.splice_value] at out
  refine ⟨c*d,mul_ne_zero hc hd,?_⟩
  convert out using 1
  funext x
  dsimp only [phase]
  ring

theorem even (f : Signature K 4) (hf : EvenSupport f) (t : K) (i : Fin 4) : EvenSupport (phase f t i) := by
  intro x odd
  simp [phase,hf x odd]

theorem first (f : Signature K 4) (hf : (entries f).a≠0) (t : K) (i : Fin 4) :
    (entries (phase f t i)).a≠0 := by
  have z : (![false,false,false,false] : Fin 4→Bool) i=false := by fin_cases i <;> rfl
  simpa [entries,phase,z] using hf

theorem last (f : Signature K 4) (hf : (entries f).x≠0) (t : K) (ht : t≠0) (i : Fin 4) :
    (entries (phase f t i)).x≠0 := by
  have z : (![true,true,true,true] : Fin 4→Bool) i=true := by fin_cases i <;> rfl
  simpa only [entries,phase,z,ite_true] using mul_ne_zero ht hf

theorem one_complement (f : Signature K 4)
    (b : (entries f).b=0) (y : (entries f).y=0) (d : (entries f).d=0) (w : (entries f).w=0)
    (z : (entries f).z≠0) : S.Complement (phase f ((entries f).c/(entries f).z) 0) := by
  simp only [S.Complement,entries,phase,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Bool.false_eq_true,if_false,if_true,one_mul]
  change (entries f).b=((entries f).c/(entries f).z)*(entries f).y ∧
    (entries f).c=((entries f).c/(entries f).z)*(entries f).z ∧
    (entries f).d=((entries f).c/(entries f).z)*(entries f).w
  simp [b,y,d,w,z]

theorem two_complement (f : Signature K 4)
    (b : (entries f).b=0) (y : (entries f).y=0) (z : (entries f).z≠0)
    (product : (entries f).c*(entries f).z=(entries f).d*(entries f).w) :
    S.Complement (phase (phase f ((entries f).w/(entries f).z) 2) ((entries f).d/(entries f).z) 0) := by
  simp only [S.Complement,entries,phase,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Bool.false_eq_true,if_false,if_true,one_mul]
  change ((entries f).w/(entries f).z)*(entries f).b=((entries f).d/(entries f).z)*(entries f).y ∧
    (entries f).c=((entries f).d/(entries f).z)*(((entries f).w/(entries f).z)*(entries f).z) ∧
    ((entries f).w/(entries f).z)*(entries f).d=((entries f).d/(entries f).z)*(entries f).w
  constructor
  · simp [b,y]
  constructor
  · field_simp
    linear_combination product
  · ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparsePhase
end
