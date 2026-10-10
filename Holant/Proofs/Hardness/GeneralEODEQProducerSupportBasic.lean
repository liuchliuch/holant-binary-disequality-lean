import Holant.Proofs.Hardness.EONegativeWitness
import Mathlib.Data.List.MinMax

/-! Finite odd-XOR witnesses and the elementary two-coordinate zero-moving
operation used in the support obstruction producer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupportBasic
open Holant Holant.Tractable
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- The coordinatewise sum of a finite list over the two-element field. -/
def xorList : List (Fin n → Bool) → Fin n → Bool
  | [] => fun _ => false
  | x :: xs => fun i => Bool.xor (x i) (xorList xs i)

/-- Every odd affine combination lies on the selected weak charge side. -/
def Pure (sign : EOSign) (f : Signature AlgebraicComplex n) : Prop :=
  ∀ xs : List (Fin n → Bool), Odd xs.length →
    (∀ x ∈ xs, f x ≠ 0) → 0 ≤ sign.value * charge (xorList xs)

/-- Two supported words differ on exactly the indicated two coordinates. -/
structure TwoFlip (f : Signature AlgebraicComplex n) (i j : Fin n) where
  first : Fin n → Bool
  second : Fin n → Bool
  first_supported : f first ≠ 0
  second_supported : f second ≠ 0
  distinct : i ≠ j
  differs : ∀ k, first k ≠ second k ↔ k = i ∨ k = j

def spin (b : Bool) : ℤ := if b then 1 else -1

theorem charge_sum (x : Fin n → Bool) : charge x = ∑ k, spin (x k) := by
  unfold charge weight spin
  simp only [Nat.cast_sum]
  rw [Finset.mul_sum]
  have h : (n : ℤ) = ∑ _ : Fin n, (1 : ℤ) := by simp
  rw [h, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases x k <;> norm_num

theorem central_charge {f : Signature AlgebraicComplex n}
    (he : Signature.CentralSupport f) {x : Fin n → Bool} (hx : f x ≠ 0) :
    charge x = 0 := by
  have h : 2 * weight x = n := by
    by_contra hn
    exact hx (he x hn)
  unfold charge
  omega

theorem charge_change (x y : Fin n → Bool) (i j : Fin n) (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → y k = x k) :
    charge y - charge x = spin (y i) - spin (x i) +
      (spin (y j) - spin (x j)) := by
  rw [charge_sum, charge_sum, ← Finset.sum_sub_distrib]
  have hs : (∑ k ∈ ({i,j} : Finset (Fin n)), (spin (y k) - spin (x k))) =
      ∑ k : Fin n, (spin (y k) - spin (x k)) := by
    apply Finset.sum_subset (by simp)
    intro k _ hk
    have hki : k ≠ i := fun hh => hk (by simp [hh])
    have hkj : k ≠ j := fun hh => hk (by simp [hh])
    rw [h k hki hkj, sub_self]
  rw [← hs]
  simp [hij]
  ring

theorem TwoFlip.xor_apply {f : Signature AlgebraicComplex n} {i j : Fin n}
    (T : TwoFlip f i j) (x : Fin n → Bool) (k : Fin n) :
    tripleXor x T.first T.second k = if k = i ∨ k = j then !(x k) else x k := by
  have h := T.differs k
  unfold tripleXor
  by_cases hk : k = i ∨ k = j
  · have hd := h.mpr hk
    simp only [ite_eq_left hk]
    cases hx : x k <;> cases hf : T.first k <;> cases hg : T.second k <;> simp_all
  · have hd : T.first k = T.second k := by simpa using mt h.mp hk
    simp [hk, hd]

theorem TwoFlip.charge_xor {f : Signature AlgebraicComplex n} {i j : Fin n}
    (T : TwoFlip f i j) (x : Fin n → Bool) :
    charge (tripleXor x T.first T.second) =
      charge x - 2 * spin (x i) - 2 * spin (x j) := by
  have h := charge_change x (tripleXor x T.first T.second) i j T.distinct (by
    intro k hki hkj
    simp [T.xor_apply, hki, hkj])
  simp only [T.xor_apply, true_or, or_true, ite_true] at h
  have hi : spin (!(x i)) = -spin (x i) := by cases x i <;> rfl
  have hj : spin (!(x j)) = -spin (x j) := by cases x j <;> rfl
  rw [hi, hj] at h
  omega

/-- A supported distance-two move forbids two ones throughout a positive support. -/
theorem TwoFlip.not_both_true {f : Signature AlgebraicComplex n} {i j : Fin n}
    (T : TwoFlip f i j) (he : Signature.CentralSupport f)
    (hs : EONegativeWitness.Supports .positive ⟨n,f⟩)
    {x : Fin n → Bool} (hx : f x ≠ 0) : ¬(x i = true ∧ x j = true) := by
  rintro ⟨hi,hj⟩
  have hc := T.charge_xor x
  rw [central_charge he hx, hi, hj] at hc
  norm_num [spin] at hc
  rcases hs x T.first T.second hx T.first_supported T.second_supported with hp|hp
  · have hz := central_charge he hp
    omega
  · change 0 < 1 * charge (tripleXor x T.first T.second) at hp
    omega

/-- Move a possible one from the first coordinate to the second. -/
def move (i j : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun k => if k = i then false else if k = j then Bool.xor (x i) (x j) else x k

theorem move_eq_self {i j : Fin n} {x : Fin n → Bool} (hi : x i = false) :
    move i j x = x := by
  funext k
  by_cases hki : k = i
  · subst k; simp [move, hi]
  · by_cases hkj : k = j
    · subst k; simp [move, hki, hi]
    · simp [move, hki, hkj]

theorem TwoFlip.move_supported {f : Signature AlgebraicComplex n} {i j : Fin n}
    (T : TwoFlip f i j) (he : Signature.CentralSupport f)
    (hs : EONegativeWitness.Supports .positive ⟨n,f⟩)
    {x : Fin n → Bool} (hx : f x ≠ 0) : f (move i j x) ≠ 0 := by
  by_cases hi : x i = false
  · simpa [move_eq_self hi] using hx
  · have hit : x i = true := by cases hxi : x i <;> simp_all
    have hj : x j = false := by
      have hn := T.not_both_true he hs hx
      cases hxj : x j <;> simp_all
    have hm : move i j x = tripleXor x T.first T.second := by
      funext k
      rw [T.xor_apply]
      by_cases hki : k = i
      · subst k; simp [move, hit]
      · by_cases hkj : k = j
        · subst k; simp [move, hki, hit, hj]
        · simp [move, hki, hkj]
    rw [hm]
    have hz : charge (tripleXor x T.first T.second) = 0 := by
      rw [T.charge_xor, central_charge he hx, hit, hj]
      norm_num [spin]
    rcases hs x T.first T.second hx T.first_supported T.second_supported with hh|hh
    · exact hh
    · simp [EOSign.value, hz] at hh

@[simp] theorem xorList_nil : xorList ([] : List (Fin n → Bool)) = fun _ => false := rfl
@[simp] theorem xorList_cons (x : Fin n → Bool) (xs : List (Fin n → Bool)) (i : Fin n) :
    xorList (x :: xs) i = Bool.xor (x i) (xorList xs i) := rfl

theorem xorList_move (i j : Fin n) (_hij : i ≠ j) (xs : List (Fin n → Bool)) :
    xorList (xs.map (move i j)) = move i j (xorList xs) := by
  induction xs with
  | nil =>
    funext k
    simp [move]
  | cons x xs ih =>
    funext k
    simp only [List.map_cons, xorList_cons, ih]
    by_cases hki : k = i
    · subst k; simp [move]
    · by_cases hkj : k = j
      · subst k
        simp only [move, ite_eq_right hki, ite_true, xorList_cons]
        cases x i <;> cases x j <;> cases xorList xs i <;> cases xorList xs j <;> rfl
      · simp [move, hki, hkj]

def active (xs : List (Fin n → Bool)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ x ∈ xs, x i = true)

@[simp] theorem mem_active (xs : List (Fin n → Bool)) (i : Fin n) :
    i ∈ active xs ↔ ∃ x ∈ xs, x i = true := by simp [active]

theorem active_move_subset (i j : Fin n) (xs : List (Fin n → Bool))
    (hj : j ∈ active xs) : active (xs.map (move i j)) ⊆ active xs := by
  intro k hk
  obtain ⟨y,hy,hyk⟩ := (mem_active _ _).mp hk
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  by_cases hki : k = i
  · subst k; simp [move] at hyk
  · by_cases hkj : k = j
    · simpa [hkj] using hj
    · exact (mem_active _ _).mpr ⟨x,hx,by simpa [move,hki,hkj] using hyk⟩

theorem active_move_lt (i j : Fin n) (xs : List (Fin n → Bool))
    (hi : i ∈ active xs) (hj : j ∈ active xs) :
    (active (xs.map (move i j))).card < (active xs).card := by
  apply Finset.card_lt_card
  refine (active_move_subset i j xs hj).ssubset_of_ne ?_
  intro h
  have him : i ∈ active (xs.map (move i j)) := h.symm ▸ hi
  obtain ⟨x,hx,hxi⟩ := (mem_active _ _).mp him
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  simp [move] at hxi

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupportBasic
