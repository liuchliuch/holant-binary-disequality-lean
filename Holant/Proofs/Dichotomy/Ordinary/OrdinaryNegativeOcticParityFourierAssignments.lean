import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticParityFourierSemantics

/-! Every assignment to the51 private variables appears exactly once in the
literal Fourier sum. This is a proved finite equivalence, not a cardinality
assumption or a restriction on the caller's old variables. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourierAssignments
open Holant
open OrdinaryNegativeOcticParityFourier OrdinaryNegativeOcticParityFourierSemantics
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

abbrev Free := (Fin 25 → Bool×Bool) × Bool
abbrev Words (x : Fin 3 → Bool) := {w : Fin 54 → Bool //
  ∀i : Fin 3,w ⟨i.val,by omega⟩=x i}

def bits (w : Fin 54 → Bool) (v : Fin 25) : Bool×Bool :=
  (w ⟨center v,by unfold center; omega⟩,w ⟨phase v,by unfold phase; omega⟩)

def word (x : Fin 3 → Bool) (y : Free) : Words x :=
  ⟨fun i=>assignment x y.1 y.2 i.val,fun i=>assignment_logical x y.1 y.2 i⟩

theorem recover (x : Fin 3 → Bool) (w : Words x) (i : Fin 54) :
    assignment x (bits w.val) (w.val 53) i.val=w.val i := by
  by_cases hi : i.val<3
  · have h := w.property ⟨i.val,hi⟩
    simpa only [assignment,dif_pos hi] using h.symm
  by_cases hj : i.val<53
  · let v : Fin 25 := ⟨(i.val-3)/2,by omega⟩
    by_cases hm : (i.val-3)%2=0
    · have hv : i.val=center v := by dsimp [center,v]; omega
      rw [hv,assignment_center]
      exact congrArg w.val (Fin.ext hv.symm)
    · have hv : i.val=phase v := by
        have hr := Nat.mod_lt (i.val-3) (by decide : 0<2)
        dsimp [phase,v]
        omega
      rw [hv,assignment_phase]
      exact congrArg w.val (Fin.ext hv.symm)
  · have hv : i.val=constant := by unfold constant; omega
    rw [hv,assignment_constant]
    exact congrArg w.val (Fin.ext hv.symm)

def equivalence (x : Fin 3 → Bool) : Free ≃ Words x where
  toFun := word x
  invFun w := (bits w.val,w.val 53)
  left_inv y := by
    rcases y with ⟨b,c⟩
    apply Prod.ext
    · funext v
      apply Prod.ext <;> simp [bits,word]
    · change assignment x b c constant=c
      exact assignment_constant x b c
  right_inv w := by
    apply Subtype.ext
    funext i
    exact recover x w i

/-- Exact change of variables for any evaluator on the literal54 addresses. -/
theorem sum_words {K : Type*} [AddCommMonoid K] (x : Fin 3 → Bool)
    (f : Words x → K) :
    (∑w : Words x,f w)=∑y : Free,f (word x y) := by
  classical
  exact ((equivalence x).sum_comp f).symm
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourierAssignments
end
