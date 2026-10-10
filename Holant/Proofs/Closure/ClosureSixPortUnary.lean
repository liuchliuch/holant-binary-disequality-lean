import Holant.Proofs.Closure.ClosureSixPortZero

/-! NEW UNVERIFIED direct unary support lowering. The residual factor is the
literal slice of the given six-port tensor; no desired target is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
open Holant.LocalDrafts.FinitePGL2.Stabilization

def pointMass (b : Bool) : Signature ℂ 1 := fun x => if x 0 = b then 1 else 0

def unaryResidual (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (b : Bool) : Signature ℂ 5 :=
  fun x => h (fun i => (Fin.cons b x : Word 6) (e.symm i))

theorem oneRightPort (i : Fin 5) :
    (finSumFinEquiv (.inr i) : Fin (1+5)) = i.succ := by
  apply Fin.ext
  simp only [finSumFinEquiv_apply_right,Fin.val_natAdd,Fin.val_succ]
  omega

/-- A fixed actual supported bit gives the exact 1+5 factorization. -/
def splitOneFive (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (b : Bool)
    (fixed : ∀ w : Word 6, h w ≠ 0 → w (e 0) = b) :
    ProperSplit (⟨6,h⟩ : AnySignature ℂ) ⟨1,pointMass b⟩ ⟨5,unaryResidual h e b⟩ where
  left_pos := by norm_num
  right_pos := by norm_num
  ports := finSumFinEquiv.trans e
  scale := 1
  equation := by
    funext w
    have leftZero : Fin.castAdd 5 (0 : Fin 1) = (0 : Fin 6) := rfl
    simp only [Units.val_one,one_mul,pointMass,unaryResidual,Equiv.trans_apply,
      finSumFinEquiv_apply_left,leftZero,oneRightPort]
    by_cases hb : w (e 0) = b
    · rw [if_pos hb,one_mul]
      congr 1
      funext i
      obtain ⟨j,rfl⟩ := e.surjective i
      simp only [Equiv.symm_apply_apply]
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.cons_zero] using hb
      · rfl
    · rw [if_neg hb,zero_mul]
      exact Classical.byContradiction (fun hn => hb (fixed w hn))

theorem fixed_port_not_prime (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (b : Bool)
    (fixed : ∀ w : Word 6, h w ≠ 0 → w (e 0) = b) :
    ¬ Prime (⟨6,h⟩ : AnySignature ℂ) :=
  fun hp => hp.2 ⟨⟨1,pointMass b⟩,⟨5,unaryResidual h e b⟩,⟨splitOneFive h e b fixed⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
