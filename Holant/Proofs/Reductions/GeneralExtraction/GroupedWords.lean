import Holant.Proofs.Reductions.GeneralExtraction.Carrier
import Mathlib.Data.List.GetD


namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GroupedWords
open scoped BigOperators
variable {K : Type*} [CommSemiring K] {n : ℕ}

def word (f : Signature K n) (bits : List Bool) : K :=
  f (fun i => bits.getD i.val false)

def power (f : Signature K n) : ℕ → List Bool → K
  | 0, _ => 1
  | k + 1, bits => word f bits * power f k (bits.drop n)

theorem getD_drop {α : Type*} (xs : List α) (d : α) (a i : ℕ) :
    (xs.drop a).getD i d = xs.getD (a + i) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem word_append (f : Signature K n) (xs ys : List Bool)
    (hx : xs.length = n) : word f (xs ++ ys) = word f xs := by
  unfold word
  apply congrArg f
  funext i
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (show i.val < xs.length by simpa [hx] using i.isLt)]

/-- No assumption about the value of a grouped vertex: it is the tensor
product defined in Carrier, with copy-major ordered ports. -/
theorem power_eq_blockPower (f : Signature K n) (k : ℕ) (bits : List Bool) :
    power f k bits = Carrier.blockPower f k (fun i => bits.getD i.val false) := by
  induction k generalizing bits with
  | zero => simp [power, Carrier.blockPower]
  | succ k ih =>
    rw [power, ih]
    unfold Carrier.blockPower
    rw [Fin.prod_univ_succ]
    refine congrArg₂ (· * ·) ?_ ?_
    · unfold word
      apply congrArg f
      funext i
      simp [finProdFinEquiv]
    · apply Finset.prod_congr rfl
      intro j _
      apply congrArg f
      funext i
      simp [getD_drop, finProdFinEquiv, Nat.mul_add, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem power_flatten (f : Signature K n) (words : List (List Bool))
    (hw : ∀ w ∈ words, w.length = n) :
    power f words.length words.flatten = (words.map (word f)).prod := by
  induction words with
  | nil => simp [power]
  | cons w ws ih =>
    have hl := hw w (by simp)
    have ht := ih (fun v hv => hw v (by simp [hv]))
    simp only [List.length_cons, List.flatten_cons, power, List.map_cons, List.prod_cons]
    rw [word_append f w ws.flatten hl]
    have hd : (w ++ ws.flatten).drop n = ws.flatten := by
      rw [← hl, List.drop_left]
    rw [hd, ht]

theorem flatMap_length {α β : Type*} (g : α → List β) (xs : List α)
    (h : ∀ x ∈ xs, (g x).length = n) : (xs.flatMap g).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rw [Nat.succ_mul]
    exact Nat.add_comm _ _

end Holant.LocalDrafts.Hardness.GeneralExtraction.GroupedWords
