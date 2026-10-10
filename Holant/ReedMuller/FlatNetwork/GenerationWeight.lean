import Holant.ReedMuller.FlatNetwork.Transvection
import Mathlib.Data.Finset.Card

/-! The elementary weight reduction used by the converse in Lemma 7.14.
Every reducing vector has exactly four nonzero coordinates. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def wordSupport (x : BinaryVector n) : Finset (Fin n) := Finset.univ.filter fun i => x i = 1

def supportWord (S : Finset (Fin n)) : BinaryVector n := fun i => if i ∈ S then 1 else 0

@[simp] theorem mem_wordSupport (x : BinaryVector n) (i : Fin n) :
    i ∈ wordSupport x ↔ x i = 1 := by simp [wordSupport]

@[simp] theorem wordSupport_supportWord (S : Finset (Fin n)) :
    wordSupport (supportWord S) = S := by
  ext i
  simp [supportWord]

@[simp] theorem supportWord_wordSupport (x : BinaryVector n) :
    supportWord (wordSupport x) = x := by
  funext i
  have H : ∀ a : ZMod 2, (if a = 1 then 1 else 0) = a := by decide
  simpa [supportWord] using H (x i)

@[simp] theorem binaryWeight_supportWord (S : Finset (Fin n)) :
    binaryWeight (supportWord S) = S.card := by
  change (wordSupport (supportWord S)).card = _
  rw [wordSupport_supportWord]

theorem dot_supportWord (x : BinaryVector n) (S : Finset (Fin n)) :
    dot x (supportWord S) = ∑ i ∈ S, x i := by
  simp [dot, supportWord, Finset.sum_ite_mem]

theorem dot_supportWord_of_subset (x : BinaryVector n) (S : Finset (Fin n))
    (hS : S ⊆ wordSupport x) : dot x (supportWord S) = (S.card : ZMod 2) := by
  rw [dot_supportWord]
  have h : ∀ i ∈ S, x i = 1 := fun i hi => (mem_wordSupport x i).mp (hS hi)
  simp [Finset.sum_congr rfl h]

theorem binaryWeight_le (x : BinaryVector n) : binaryWeight x ≤ n := by
  change (wordSupport x).card ≤ n
  simpa only [Fintype.card_fin] using Finset.card_le_univ (wordSupport x)

theorem binaryWeight_pos_iff (x : BinaryVector n) : 0 < binaryWeight x ↔ x ≠ 0 := by
  constructor
  · intro hx hz
    subst x
    simpa [binaryWeight] using hx
  · intro hx
    by_contra hn
    have hc : wordSupport x = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hn)
    have H := supportWord_wordSupport x
    rw [hc] at H
    apply hx
    rw [← H]
    funext i
    simp [supportWord]

theorem binaryWeight_lt_iff (x : BinaryVector n) : binaryWeight x < n ↔ x ≠ ones n := by
  constructor
  · intro hx hz
    subst x
    simpa [binaryWeight, ones] using hx
  · intro hx
    have hle := binaryWeight_le x
    by_contra hn
    have hc : (wordSupport x).card = Fintype.card (Fin n) := by
      change binaryWeight x = Fintype.card (Fin n)
      simp only [Fintype.card_fin]
      omega
    have hs : wordSupport x = Finset.univ := (Finset.card_eq_iff_eq_univ (wordSupport x)).mp hc
    have H := supportWord_wordSupport x
    rw [hs] at H
    apply hx
    rw [← H]
    funext i
    simp [supportWord, ones]

/-- Three ones and one zero give an actual weight-four orthogonal
transvection, decreasing the word weight by exactly two. -/
theorem exists_weightFour_reduction (x : BinaryVector n)
    (hlarge : 2 < binaryWeight x) (hzero : binaryWeight x < n) :
    ∃ s : BinaryVector n, binaryWeight s = 4 ∧ dot s s = 0 ∧
      binaryWeight (transvection s x) + 2 = binaryWeight x := by
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ (wordSupport x).card by
    change 3 ≤ binaryWeight x
    omega)
  have hn : wordSupport x ≠ Finset.univ := by
    intro he
    have H : binaryWeight x = n := by change (wordSupport x).card = n; rw [he]; simp
    omega
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b ∉ wordSupport x := by
    by_contra h
    apply hn
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  have hbT : b ∉ T := fun h => hb (hT h)
  have hxb : x b = 0 := by
    have hne : x b ≠ 1 := by simpa using hb
    have H : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
    exact H _ hne
  let s := supportWord (insert b T)
  have hs : binaryWeight s = 4 := by simp [s, hbT, hcard]
  have hss : dot s s = 0 := by rw [← cast_binaryWeight, hs]; decide
  have hxs : dot x s = 1 := by
    rw [show s = supportWord (insert b T) from rfl, dot_supportWord, Finset.sum_insert hbT,
      hxb, zero_add, ← dot_supportWord, dot_supportWord_of_subset x T hT, hcard]
    decide
  have ht : transvection s x = supportWord (insert b (wordSupport x \ T)) := by
    rw [transvection, hxs, one_smul]
    funext i
    by_cases hib : i = b
    · subst i
      simp [s, supportWord, hxb]
    · by_cases hiT : i ∈ T
      · have hxi : x i = 1 := (mem_wordSupport x i).mp (hT hiT)
        simp [s, supportWord, hib, hiT, hxi, add_self_zero]
      · by_cases hi : i ∈ wordSupport x
        · have hxi : x i = 1 := (mem_wordSupport x i).mp hi
          simp [s, supportWord, hib, hiT, hi, hxi]
        · have hxi : x i = 0 := by
            have hne : x i ≠ 1 := by simpa using hi
            have H : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
            exact H _ hne
          simp [s, supportWord, hib, hiT, hi, hxi]
  refine ⟨s, hs, hss, ?_⟩
  rw [ht, binaryWeight_supportWord, Finset.card_insert_of_notMem (by simp [hb]),
    Finset.card_sdiff_of_subset hT, hcard]
  change binaryWeight x - 3 + 1 + 2 = binaryWeight x
  omega

end
end Holant.ReedMuller.FlatNetwork
