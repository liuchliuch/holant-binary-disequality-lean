import Holant.Proofs.Closure.ClosureSixPortZero

/-! NEW UNVERIFIED exact Z/C assembly. This helper consumes the literal
fixed-factor payload to be INTERNALLY obtained from the sampled root pencil.
It is not a substitute for that missing ruling theorem in the closed base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
open Holant.LocalDrafts.FinitePGL2.Stabilization

theorem zeroSector_word (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (zero : ZeroSector h e p) (w : Word 6) (parity : (w (e 0) ^^ w (e 1))=p) : h w=0 := by
  have endpoint : sliceSix h e p (w (e 0)) = 0 := by
    cases w (e 0)
    · exact zero.1
    · exact zero.2
  have reconstruct : fillSix e (w (e 0)) p (residualSix e w) = w := by
    rw [←parity]
    exact fillSix_reconstruct e w
  have he := congrFun endpoint (residualSix e w)
  unfold sliceSix at he
  rw [reconstruct] at he
  exact he

theorem zero_zero_tensor (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6))
    (even : ZeroSector h e false) (odd : ZeroSector h e true) : h=0 := by
  funext w
  cases hp : w (e 0) ^^ w (e 1)
  · exact zeroSector_word h e false even w hp
  · exact zeroSector_word h e true odd w hp

def liftResidual (u : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin 2)) u).trans finSumFinEquiv)

theorem liftResidual_left (u : Equiv.Perm (Fin 4)) (j : Fin 2) :
    liftResidual u ((finSumFinEquiv : (Fin 2 ⊕ Fin 4) ≃ Fin 6) (.inl j)) = (finSumFinEquiv : (Fin 2 ⊕ Fin 4) ≃ Fin 6) (.inl j) := by
  simp [liftResidual]

theorem liftResidual_right (u : Equiv.Perm (Fin 4)) (j : Fin 4) :
    liftResidual u j.succ.succ = (u j).succ.succ := by
  rw [←rightPort,←rightPort]
  simp [liftResidual]

def fixedFactorOrder (e : Equiv.Perm (Fin 6)) (u : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  ((Equiv.swap (0 : Fin 6) 2).trans (Equiv.swap 1 3)).trans ((liftResidual u).trans e)

theorem fixedFactorOrder_first (e : Equiv.Perm (Fin 6)) (u : Equiv.Perm (Fin 4)) :
    fixedFactorOrder e u 0 = e (u 0).succ.succ := by
  change e (liftResidual u 2) = _
  exact congrArg e (liftResidual_right u 0)

theorem fixedFactorOrder_second (e : Equiv.Perm (Fin 6)) (u : Equiv.Perm (Fin 4)) :
    fixedFactorOrder e u 1 = e (u 1).succ.succ := by
  change e (liftResidual u 3) = _
  exact congrArg e (liftResidual_right u 1)

theorem fixedFactorOrder_third (e : Equiv.Perm (Fin 6)) (u : Equiv.Perm (Fin 4)) :
    fixedFactorOrder e u 2 = e 0 := by
  change e (liftResidual u ((finSumFinEquiv : (Fin 2 ⊕ Fin 4) ≃ Fin 6) (.inl (0 : Fin 2)))) = _
  convert congrArg e (liftResidual_left u 0) using 1 <;> rfl

theorem fixedFactorOrder_fourth (e : Equiv.Perm (Fin 6)) (u : Equiv.Perm (Fin 4)) :
    fixedFactorOrder e u 3 = e 1 := by
  change e (liftResidual u ((finSumFinEquiv : (Fin 2 ⊕ Fin 4) ≃ Fin 6) (.inl (1 : Fin 2)))) = _
  convert congrArg e (liftResidual_left u 1) using 1 <;> rfl

theorem fixedFactorOrder_fifth (e : Equiv.Perm (Fin 6)) (u : Equiv.Perm (Fin 4)) :
    fixedFactorOrder e u 4 = e (u 2).succ.succ := by
  change e (liftResidual u 4) = _
  exact congrArg e (liftResidual_right u 2)

theorem fixedFactorOrder_sixth (e : Equiv.Perm (Fin 6)) (u : Equiv.Perm (Fin 4)) :
    fixedFactorOrder e u 5 = e (u 3).succ.succ := by
  change e (liftResidual u 5) = _
  exact congrArg e (liftResidual_right u 3)

structure CommonResidualFactor (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool) where
  order : Equiv.Perm (Fin 4)
  fixed : Mat
  varying : Bool → Mat
  endpoints : ∀ a x, sliceSix h e p a x =
    fixed (x (order 0)) (x (order 1)) * varying a (x (order 2)) (x (order 3))

def CommonResidualFactor.remainder {h : Signature ℂ 6} {e : Equiv.Perm (Fin 6)} {p : Bool}
    (D : CommonResidualFactor h e p) : Signature ℂ 4 := fun y =>
  if (y 0 ^^ y 1)=p then D.varying (y 0) (y 2) (y 3) else 0

/-- The fixed residual binary factors from the SAME actual six-port tensor
when the opposite sector vanishes. The 2+4 order and remaining factor are built. -/
def zero_fixed_split (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (zero : ZeroSector h e (!p)) (D : CommonResidualFactor h e p) :
    ProperSplit (⟨6,h⟩ : AnySignature ℂ) ⟨2,binaryWord D.fixed⟩ ⟨4,D.remainder⟩ where
  left_pos := by norm_num
  right_pos := by norm_num
  ports := finSumFinEquiv.trans (fixedFactorOrder e D.order)
  scale := 1
  equation := by
    funext w
    have l0 : Fin.castAdd 4 (0 : Fin 2) = (0 : Fin 6) := rfl
    have l1 : Fin.castAdd 4 (1 : Fin 2) = (1 : Fin 6) := rfl
    simp only [Units.val_one,one_mul,binaryWord,CommonResidualFactor.remainder,
      Equiv.trans_apply,finSumFinEquiv_apply_left,l0,l1,rightPort,
      ]
    have r0 : (0 : Fin 4).succ.succ = (2 : Fin 6) := rfl
    have r1 : (1 : Fin 4).succ.succ = (3 : Fin 6) := rfl
    have r2 : (2 : Fin 4).succ.succ = (4 : Fin 6) := rfl
    have r3 : (3 : Fin 4).succ.succ = (5 : Fin 6) := rfl
    simp only [r0,r1,r2,r3]
    rw [fixedFactorOrder_first,fixedFactorOrder_second,fixedFactorOrder_third,
      fixedFactorOrder_fourth,fixedFactorOrder_fifth,fixedFactorOrder_sixth]
    by_cases parity : (w (e 0) ^^ w (e 1))=p
    · rw [if_pos parity]
      have endpoint := D.endpoints (w (e 0)) (residualSix e w)
      have reconstruct : fillSix e (w (e 0)) p (residualSix e w) = w := by
        rw [←parity]
        exact fillSix_reconstruct e w
      unfold sliceSix at endpoint
      rw [reconstruct] at endpoint
      exact endpoint
    · rw [if_neg parity,mul_zero]
      have complementary : (w (e 0) ^^ w (e 1))=(!p) := by
        cases p <;> cases h0 : w (e 0) <;> cases h1 : w (e 1) <;> simp_all
      have endpoint : sliceSix h e (!p) (w (e 0)) = 0 := by
        cases w (e 0)
        · exact zero.1
        · exact zero.2
      have reconstruct : fillSix e (w (e 0)) (!p) (residualSix e w) = w := by
        rw [←complementary]
        exact fillSix_reconstruct e w
      have he := congrFun endpoint (residualSix e w)
      unfold sliceSix at he
      rw [reconstruct] at he
      exact he

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
