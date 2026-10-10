import Holant.Proofs.CountingMachines.StandardMachine.Support.Cost
import Holant.Complexity.GraphPreprocessing.FiniteRecode

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Internally fixed finite symbol tables. These list-valued
functions specify the representation and label static syntax-tree leaves; no
List, finite alphabet symbol, or decoder is a Boolean-stack runtime primitive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Code
open Turing Computability Holant.Complexity
variable (m : BinaryMachine)
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

def width (k : m.core.K) : ℕ := Fintype.card (m.core.Γ k)+1
def bit (k : m.core.K) (a : m.core.Γ k) (i : Fin (width m k)) : Bool :=
  decide ((Fintype.equivFin (m.core.Γ k) a).val = i.val)
def symbol (k : m.core.K) (a : m.core.Γ k) : List Bool := List.ofFn (bit m k a)
def word (k : m.core.K) (xs : List (m.core.Γ k)) : List Bool := xs.flatMap (symbol m k)

@[simp] theorem width_pos (k : m.core.K) : 0 < width m k := by simp [width]
@[simp] theorem symbol_length (k : m.core.K) (a : m.core.Γ k) :
    (symbol m k a).length = width m k := List.length_ofFn

theorem symbol_injective (k : m.core.K) : Function.Injective (symbol m k) := by
  intro a b h
  have hf : bit m k a = bit m k b := List.ofFn_injective h
  let i : Fin (width m k) := ⟨(Fintype.equivFin (m.core.Γ k) a).val,by
    have ha := (Fintype.equivFin (m.core.Γ k) a).isLt
    simp only [width]
    omega⟩
  have hb : (Fintype.equivFin (m.core.Γ k) b).val =
      (Fintype.equivFin (m.core.Γ k) a).val := by
    have hi := congrFun hf i
    simpa [bit,i] using hi.symm
  exact (Fintype.equivFin (m.core.Γ k)).injective (Fin.ext hb.symm)

@[simp] theorem word_length (k : m.core.K) (xs : List (m.core.Γ k)) :
    (word m k xs).length = width m k*xs.length := by
  induction xs with
  | nil => simp [word]
  | cons a xs ih => simp [word,List.flatMap_cons,symbol_length,ih,Nat.mul_succ,Nat.mul_comm,Nat.add_comm,Nat.mul_add]

theorem word_injective (k : m.core.K) : Function.Injective (word m k) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    have hl := congrArg List.length h
    simp only [word_length,List.length_nil,Nat.mul_zero] at hl
    have hy : ys.length = 0 := by
      rcases Nat.mul_eq_zero.mp hl.symm with hw | hy
      · exact False.elim ((Nat.ne_of_gt (width_pos m k)) hw)
      · exact hy
    exact (List.length_eq_zero_iff.mp hy).symm
  | cons a xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have hl := congrArg List.length h
      simp only [word_length,List.length_cons,List.length_nil,Nat.mul_zero] at hl
      exact False.elim ((Nat.ne_of_gt (Nat.mul_pos (width_pos m k) (Nat.succ_pos xs.length))) hl)
    | cons b ys =>
      have hp := congrArg (List.take (width m k)) h
      have hs : symbol m k a = symbol m k b := by
        simpa [word,List.flatMap_cons,List.take_append,symbol_length] using hp
      have hab : a = b := symbol_injective m k hs
      subst b
      have hr : word m k xs = word m k ys :=
        List.append_cancel_left (by simpa only [word,List.flatMap_cons] using h)
      simp only [ih hr]

/-- Evaluated only on the fixed word naming a statically constructed leaf. -/
def decode (k : m.core.K) (bits : List Bool) : Option (m.core.Γ k) :=
  if h : ∃ a, symbol m k a = bits then some (Classical.choose h) else none

@[simp] theorem decode_symbol (k : m.core.K) (a : m.core.Γ k) :
    decode m k (symbol m k a) = some a := by
  have h : ∃ b, symbol m k b = symbol m k a := ⟨a,rfl⟩
  rw [decode,dif_pos h]
  exact congrArg some (symbol_injective m k (Classical.choose_spec h))

theorem decode_sound (k : m.core.K) (bits : List Bool) (a : m.core.Γ k)
    (h : decode m k bits = some a) : symbol m k a = bits := by
  unfold decode at h
  split at h
  · rename_i he
    have ha := Option.some.inj h
    simpa only [ha] using Classical.choose_spec he
  · cases h

def tapes (S : ∀ k, List (m.core.Γ k)) : m.core.K → List Bool := fun k => word m k (S k)

theorem update_tapes (S : ∀ k, List (m.core.Γ k)) (k : m.core.K)
    (xs : List (m.core.Γ k)) :
    Function.update (tapes m S) k (word m k xs) = tapes m (Function.update S k xs) := by
  funext j
  by_cases hj : j = k
  · subst j; simp [tapes]
  · simp [tapes,hj]

theorem tapes_injective : Function.Injective (tapes m) := by
  intro S U h
  funext k
  exact word_injective m k (congrFun h k)

theorem tapes_cons (S : ∀ k, List (m.core.Γ k)) (k : m.core.K) (a : m.core.Γ k) :
    Function.update (tapes m S) k (symbol m k a++tapes m S k) =
      tapes m (Function.update S k (a::S k)) := by
  simpa only [tapes,word,List.flatMap_cons] using update_tapes m S k (a::S k)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Code
