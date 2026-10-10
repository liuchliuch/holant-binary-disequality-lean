import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases

/-!
The finite Boolean support step of Lemma 6.27.  The hypotheses describe the
actual zero patterns of every deleted-pair pencil; parity and complementary
closure are conclusions, not assumptions.  All proofs are kernel checked.
-/
namespace Holant.Marked.SupportAtlas

abbrev Word := Fin 4 → Bool

/-- The total Boolean parity of a four-port word. -/
def parity (w : Word) : Bool := (w 0 ^^ w 1) ^^ (w 2 ^^ w 3)

/-- Simultaneously flip all four coordinates. -/
def complement (w : Word) : Word := fun i => !(w i)

/-- An ordered deleted pair occupies `e 0,e 1`; the residual pair occupies
`e 2,e 3`. The first pair has prescribed parity `p`. -/
def fill (e : Equiv.Perm (Fin 4)) (a p b c : Bool) : Word :=
  fun i => (![a, a ^^ p, b, c] : Word) (e.symm i)

/-- The six support patterns of the two pencil endpoints, read row by row. -/
def AllowedPattern (M : Bool → Bool → Bool) : Prop :=
  (M false false = false ∧ M false true = false ∧
    M true false = false ∧ M true true = false) ∨
  (M false false = true ∧ M false true = true ∧
    M true false = false ∧ M true true = false) ∨
  (M false false = false ∧ M false true = false ∧
    M true false = true ∧ M true true = true) ∨
  (M false false = true ∧ M false true = true ∧
    M true false = true ∧ M true true = true) ∨
  (M false false = true ∧ M false true = false ∧
    M true false = false ∧ M true true = true) ∨
  (M false false = false ∧ M false true = true ∧
    M true false = true ∧ M true true = false)

instance (M : Bool → Bool → Bool) : Decidable (AllowedPattern M) := by
  unfold AllowedPattern
  infer_instance

/-- Both endpoints lie in one residual parity plane, and their two axis
supports have one of the six permitted zero patterns. -/
def PencilSupport (q : Word → Bool) (e : Equiv.Perm (Fin 4)) (p : Bool) : Prop :=
  ∃ r : Bool,
    (∀ a b c : Bool, (b ^^ c) ≠ r → q (fill e a p b c) = false) ∧
    AllowedPattern (fun a b => q (fill e a p b (b ^^ r)))

/-- This includes every deleted pair and both of its orientations. -/
def DeckSupport (q : Word → Bool) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (p : Bool), PencilSupport q e p

@[simp] theorem fill_at_zero (e : Equiv.Perm (Fin 4)) (a p b c : Bool) :
    fill e a p b c (e 0) = a := by simp only [fill, Equiv.symm_apply_apply]; rfl
@[simp] theorem fill_at_one (e : Equiv.Perm (Fin 4)) (a p b c : Bool) :
    fill e a p b c (e 1) = (a ^^ p) := by simp only [fill, Equiv.symm_apply_apply]; rfl
@[simp] theorem fill_at_two (e : Equiv.Perm (Fin 4)) (a p b c : Bool) :
    fill e a p b c (e 2) = b := by simp only [fill, Equiv.symm_apply_apply]; rfl
@[simp] theorem fill_at_three (e : Equiv.Perm (Fin 4)) (a p b c : Bool) :
    fill e a p b c (e 3) = c := by simp only [fill, Equiv.symm_apply_apply]; rfl

theorem fill_reconstruct (e : Equiv.Perm (Fin 4)) (w : Word) :
    fill e (w (e 0)) (w (e 0) ^^ w (e 1)) (w (e 2)) (w (e 3)) = w := by
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp only [fill, Equiv.symm_apply_apply]
  fin_cases j <;> simp

/-- A supported word determines the residual plane of its deleted-parity slice. -/
theorem residual_eq_of_nonzero {q : Word → Bool} {e : Equiv.Perm (Fin 4)}
    {w : Word} {r : Bool}
    (hzero : ∀ a b c : Bool, (b ^^ c) ≠ r →
      q (fill e a (w (e 0) ^^ w (e 1)) b c) = false)
    (hw : q w = true) : (w (e 2) ^^ w (e 3)) = r := by
  by_contra h
  have hz := hzero (w (e 0)) (w (e 2)) (w (e 3)) h
  rw [fill_reconstruct, hw] at hz
  contradiction

/-- For a fixed deleted parity, all supported words have the same residual parity. -/
theorem residual_eq {q : Word → Bool} (h : DeckSupport q)
    (e : Equiv.Perm (Fin 4)) {w v : Word} (hw : q w = true) (hv : q v = true)
    (heq : (w (e 0) ^^ w (e 1)) = (v (e 0) ^^ v (e 1))) :
    (w (e 2) ^^ w (e 3)) = (v (e 2) ^^ v (e 3)) := by
  obtain ⟨r, hz, _⟩ := h e (w (e 0) ^^ w (e 1))
  exact (residual_eq_of_nonzero hz hw).trans
    (residual_eq_of_nonzero (by simpa only [heq] using hz) hv).symm

private theorem three_splits : ∀ a b c d A B C D : Bool,
    ((a ^^ b) = (A ^^ B) → (c ^^ d) = (C ^^ D)) →
    ((a ^^ c) = (A ^^ C) → (b ^^ d) = (B ^^ D)) →
    ((c ^^ b) = (C ^^ B) → (a ^^ d) = (A ^^ D)) →
    ((a ^^ b) ^^ (c ^^ d)) = ((A ^^ B) ^^ (C ^^ D)) := by decide

/-- The complete pencil constraints force a single total parity on the support. -/
theorem parity_eq {q : Word → Bool} (h : DeckSupport q)
    {w v : Word} (hw : q w = true) (hv : q v = true) : parity w = parity v := by
  apply three_splits (w 0) (w 1) (w 2) (w 3) (v 0) (v 1) (v 2) (v 3)
  · exact residual_eq h (Equiv.refl _) hw hv
  · simpa [Equiv.swap_apply_def] using residual_eq h (Equiv.swap (1 : Fin 4) 2) hw hv
  · simpa [Equiv.swap_apply_def] using residual_eq h (Equiv.swap (0 : Fin 4) 2) hw hv

namespace AllowedPattern

/-- Any choice of two constant rows is one of the permitted patterns. -/
theorem row_constant {M : Bool → Bool → Bool}
    (h : ∀ a : Bool, M a false = M a true) : AllowedPattern M := by
  have h0 := h false
  have h1 := h true
  cases hff : M false false <;> cases htf : M true false <;>
    simp_all [AllowedPattern]

/-- Empty, full, and the two pairs of complementary singleton axes are permitted. -/
theorem centrally_symmetric {M : Bool → Bool → Bool}
    (hdiag : M false false = M true true)
    (hoff : M false true = M true false) : AllowedPattern M := by
  cases hff : M false false <;> cases hft : M false true <;>
    simp_all [AllowedPattern]

/-- A permitted square whose transpose is also permitted is centrally symmetric. -/
theorem complement_of_transpose {M : Bool → Bool → Bool}
    (h : AllowedPattern M) (ht : AllowedPattern (fun a b => M b a))
    (a b : Bool) : M (!a) (!b) = M a b := by
  cases hff : M false false <;> cases hft : M false true <;>
    cases htf : M true false <;> cases htt : M true true <;>
    cases a <;> cases b <;> simp_all [AllowedPattern]

end AllowedPattern

/-- Exchange the deleted and residual ordered pairs. -/
def swapBlocks : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem fill_swapBlocks (a p b r : Bool) :
    fill swapBlocks a r b (b ^^ p) =
      fill (Equiv.refl _) b p a (a ^^ r) := by
  funext i
  fin_cases i <;> rfl

theorem fill_axis_complement (e : Equiv.Perm (Fin 4)) (a p b r : Bool) :
    fill e (!a) p (!b) ((!b) ^^ r) =
      complement (fill e a p b (b ^^ r)) := by
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp only [complement, fill, Equiv.symm_apply_apply]
  fin_cases j <;> cases a <;> cases p <;> cases b <;> cases r <;> rfl

/-- The transpose deck rules out one-full-row patterns, forcing each nonzero
entry to have its bitwise complementary entry in the support. -/
theorem complement_of_nonzero {q : Word → Bool} (h : DeckSupport q)
    {w : Word} (hw : q w = true) : q (complement w) = true := by
  obtain ⟨r, hz, hm⟩ := h (Equiv.refl _) (w 0 ^^ w 1)
  have hr : (w 2 ^^ w 3) = r := residual_eq_of_nonzero hz hw
  subst r
  obtain ⟨s, hz', hm'⟩ := h swapBlocks (w 2 ^^ w 3)
  have hs : (w 0 ^^ w 1) = s := residual_eq_of_nonzero hz' hw
  subst s
  have ht : AllowedPattern (fun a b =>
      q (fill (Equiv.refl _) b (w 0 ^^ w 1) a (a ^^ (w 2 ^^ w 3)))) := by
    simpa only [fill_swapBlocks] using hm'
  have hc := AllowedPattern.complement_of_transpose hm ht (w 0) (w 2)
  have hf : fill (Equiv.refl _) (w 0) (w 0 ^^ w 1) (w 2)
      (w 2 ^^ (w 2 ^^ w 3)) = w := by
    simpa using fill_reconstruct (Equiv.refl (Fin 4)) w
  rw [fill_axis_complement, hf, hw] at hc
  exact hc

@[simp] theorem complement_complement (w : Word) : complement (complement w) = w := by
  funext i
  simp [complement]

/-- Support is closed under simultaneous complementation, including zero entries. -/
theorem complement_eq {q : Word → Bool} (h : DeckSupport q) (w : Word) :
    q (complement w) = q w := by
  cases hw : q w
  · cases hc : q (complement w)
    · rfl
    · have hc' := complement_of_nonzero h hc
      simp [hw] at hc'
  · exact complement_of_nonzero h hw

/-- The finite support conclusion of the marked quaternary support atlas. -/
theorem classification {q : Word → Bool} (h : DeckSupport q)
    (hne : ∃ w, q w = true) :
    ∃ p : Bool, (∀ w, q w = true → parity w = p) ∧
      (∀ w, q (complement w) = q w) := by
  obtain ⟨w, hw⟩ := hne
  exact ⟨parity w, fun v hv => parity_eq h hv hw, complement_eq h⟩

/-- Four indices, one for each complementary pair in a fixed parity class. -/
abbrev PairIndex := Bool × Bool

/-- The unique member of an indexed pair whose first bit is false. -/
def representative (p : Bool) (i : PairIndex) : Word :=
  ![false, i.1, i.2, (i.1 ^^ i.2) ^^ p]

/-- Complementing a word does not change its complementary-pair index. -/
def pairIndex (w : Word) : PairIndex := (w 1 ^^ w 0, w 2 ^^ w 0)

theorem word_pair_normal_form (w : Word) :
    w = representative (parity w) (pairIndex w) ∨
      w = complement (representative (parity w) (pairIndex w)) := by
  cases h0 : w 0
  · left
    funext j
    fin_cases j <;> simp [representative, pairIndex, parity, h0]
    cases w 1 <;> cases w 2 <;> cases w 3 <;> decide
  · right
    funext j
    fin_cases j <;> simp [representative, pairIndex, parity, complement, h0]
    cases w 1 <;> cases w 2 <;> cases w 3 <;> decide

/-- Explicitly, every nonempty solution is a nonempty subset of the four
complementary word pairs in one total parity class. -/
theorem classification_pairs {q : Word → Bool} (h : DeckSupport q)
    (hne : ∃ w, q w = true) :
    ∃ (p : Bool) (selected : PairIndex → Bool),
      (∃ i, selected i = true) ∧
      ∀ w, q w = true ↔ ∃ i, selected i = true ∧
        (w = representative p i ∨ w = complement (representative p i)) := by
  obtain ⟨p, hp, hc⟩ := classification h hne
  have hiff : ∀ w, q w = true ↔ ∃ i, q (representative p i) = true ∧
      (w = representative p i ∨ w = complement (representative p i)) := by
    intro w
    constructor
    · intro hw
      have hn := word_pair_normal_form w
      rw [hp w hw] at hn
      refine ⟨pairIndex w, ?_, hn⟩
      rcases hn with hn | hn
      · rw [hn] at hw
        exact hw
      · rw [hn, hc] at hw
        exact hw
    · rintro ⟨i, hi, rfl | rfl⟩
      · exact hi
      · simpa only [hc] using hi
  obtain ⟨w, hw⟩ := hne
  obtain ⟨i, hi, _⟩ := (hiff w).mp hw
  exact ⟨p, fun i => q (representative p i), ⟨i, hi⟩, hiff⟩

end Holant.Marked.SupportAtlas
