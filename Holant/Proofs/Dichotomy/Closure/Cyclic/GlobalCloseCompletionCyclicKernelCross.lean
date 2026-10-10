import Holant.ReedMuller.CoefficientAtlas.Cards
import Mathlib.Tactic.LinearCombination

/-! Two genuine weighted matching cards cannot differ by a nontrivial
three-bit parity pencil. The proof uses their actual repeated-word values,
without assuming a matching pairing or replacing physical signatures. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicKernelCross
open Holant Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

def parity (t : Fin 3→Bool) : Bool := (t 0 ^^ t 1) ^^ t 2

theorem cross (M : WeightedMatching)
    (nonzero : ∀t : Fin 3→Bool,M.value (repeatedWord t)≠0) :
    M.value (repeatedWord ![false,false,false])*M.value (repeatedWord ![true,true,false])=
      M.value (repeatedWord ![true,false,false])*M.value (repeatedWord ![false,true,false]) := by
  rw [M.repeated_value nonzero,M.repeated_value nonzero,M.repeated_value nonzero,M.repeated_value nonzero]
  simp [Fin.prod_univ_succ]
  ring

theorem pencil_separated (M N : WeightedMatching)
    (nonzero : ∀t : Fin 3→Bool,M.value (repeatedWord t)≠0)
    (a b : ℂ) (plus : a+b≠0) (minus : a-b≠0)
    (pencil : ∀t : Fin 3→Bool,N.value (repeatedWord t)=
      (if parity t then a-b else a+b)*M.value (repeatedWord t)) : a*b=0 := by
  have nzN (t : Fin 3→Bool) : N.value (repeatedWord t)≠0 := by
    rw [pencil]
    apply mul_ne_zero _ (nonzero t)
    cases parity t <;> assumption
  have old := cross M nonzero
  have newer := cross N nzN
  simp only [pencil,parity,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Bool.false_xor,Bool.true_xor,Bool.xor_false,Bool.not_false,
    Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at newer
  let c := M.value (repeatedWord ![false,false,false])*M.value (repeatedWord ![true,true,false])
  have hc : c≠0 := mul_ne_zero (nonzero _) (nonzero _)
  have eqn : (a+b)^2*c=(a-b)^2*c := by
    calc
      _=((a+b)*M.value (repeatedWord ![false,false,false]))*
          ((a+b)*M.value (repeatedWord ![true,true,false])) := by dsimp [c];ring
      _=((a-b)*M.value (repeatedWord ![true,false,false]))*
          ((a-b)*M.value (repeatedWord ![false,true,false])) := newer
      _=(a-b)^2*(M.value (repeatedWord ![true,false,false])*M.value (repeatedWord ![false,true,false])) := by ring
      _=_ := by rw [←old]
  have square : (a+b)^2=(a-b)^2 := (mul_right_cancel₀ hc eqn)
  have hz : 4*(a*b)=0 := by linear_combination square
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicKernelCross
end
