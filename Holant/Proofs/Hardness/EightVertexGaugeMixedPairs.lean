import Holant.Proofs.Hardness.EightVertexGaugeSectorAlgebra

/-! A finite mixed-row obstruction. If every choice of two internal ports on
each row collapses one parity sector in both orientations, both rows have
constant squared port weights and their fourth-power anchors agree. Thus
different fourth-power anchors admit a live physical two-row sector choice.
This is an algebraic selection lemma, not a hardness classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeMixedPairs
variable {K : Type} [Field K]

def Collapsed (u v : Fin 4 → K) : Prop :=
  ∀ i j k l, i ≠ j → k ≠ l →
    (u i*u j+v k*v l = 0 ∨ u i*v k+u j*v l = 0) ∧
    (u i*u j+v k*v l = 0 ∨ u i*v l+u j*v k = 0)

private theorem even_zero (r s v w : K) (hv : v ≠ 0) (different : r^2 ≠ s^2)
    (cross : r*s+v*w = 0 ∨ r*v+s*w = 0)
    (straight : r*s+v*w = 0 ∨ r*w+s*v = 0) : r*s+v*w = 0 := by
  rcases cross with h | hc
  · exact h
  rcases straight with h | hs
  · exact h
  have hz : (r^2-s^2)*v = 0 := by linear_combination r*hc-s*hs
  exact ((mul_ne_zero (sub_ne_zero.mpr different) hv) hz).elim

private theorem port_alternatives (r s t v : K) (hr : r ≠ 0) (hv : v ≠ 0)
    (base : r*s+v*v = 0)
    (cap : r*t+v*v = 0 ∨ r*v+t*v = 0) : t = s ∨ t = -r := by
  rcases cap with he | ho
  · left
    apply mul_left_cancel₀ hr
    linear_combination he-base
  · right
    have hz : (r+t)*v = 0 := by linear_combination ho
    have hs := (mul_eq_zero.mp hz).resolve_right hv
    linear_combination hs

theorem squares_left [CharZero K] (u v : Fin 4 → K) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (collapsed : Collapsed u v) : ∀ i j, u i ^ 2 = u j ^ 2 := by
  intro i j
  by_contra different
  have hij : i ≠ j := by
    intro h
    exact different (congrArg (fun k => u k ^ 2) h)
  have ev (k l : Fin 4) (hkl : k ≠ l) : u i*u j+v k*v l = 0 :=
    even_zero _ _ _ _ (hv k) different
      (collapsed i j k l hij hkl).1 (collapsed i j k l hij hkl).2
  have samev : v 0 = v 1 := by
    apply mul_right_cancel₀ (hv 2)
    linear_combination ev 0 2 (by decide) - ev 1 2 (by decide)
  have base : u i*u j+v 0*v 0 = 0 := by
    simpa only [← samev] using ev 0 1 (by decide)
  have third : ∀ i j : Fin 4, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k,hki,hkj⟩ := third i j hij
  have first := (collapsed i k 0 1 (Ne.symm hki) (by decide)).1
  have second := (collapsed j k 0 1 (Ne.symm hkj) (by decide)).1
  rw [← samev] at first second
  have h1 := port_alternatives (u i) (u j) (u k) (v 0) (hu i) (hv 0) base first
  have h2 := port_alternatives (u j) (u i) (u k) (v 0) (hu j) (hv 0)
    (by simpa only [mul_comm] using base) second
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact different (congrArg (fun z : K => z^2) (h2.symm.trans h1))
  · exact hu j (by linear_combination (h2-h1)/2)
  · exact hu i (by linear_combination (h1-h2)/2)
  · have he : u i = u j := by linear_combination h1-h2
    exact different (congrArg (fun z : K => z^2) he)

theorem swap (u v : Fin 4 → K) (h : Collapsed u v) : Collapsed v u := by
  intro i j k l hij hkl
  have hh := h k l i j hkl hij
  constructor
  · simpa [mul_comm,add_comm] using hh.1
  · simpa [mul_comm,add_comm] using hh.2

private theorem equal_pair (u : Fin 4 → K) (same : ∀ i j, u i ^ 2 = u j ^ 2) :
    ∃ i j, i ≠ j ∧ u i = u j := by
  have h1 := (sq_eq_sq_iff_eq_or_eq_neg).mp (same 1 0)
  have h2 := (sq_eq_sq_iff_eq_or_eq_neg).mp (same 2 0)
  rcases h1 with h1 | h1
  · exact ⟨0,1,by decide,h1.symm⟩
  rcases h2 with h2 | h2
  · exact ⟨0,2,by decide,h2.symm⟩
  · exact ⟨1,2,by decide,h1.trans h2.symm⟩

/-- Uniform sector collapse forces common fourth-power anchors even before
assuming the separate rows have common port fourth powers. -/
theorem fourth_anchor [CharZero K] (u v : Fin 4 → K) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (collapsed : Collapsed u v) : u 0 ^ 4 = v 0 ^ 4 := by
  have su := squares_left u v hu hv collapsed
  have sv := squares_left v u hv hu (swap u v collapsed)
  obtain ⟨i,j,hij,hijv⟩ := equal_pair u su
  obtain ⟨k,l,hkl,hklv⟩ := equal_pair v sv
  have h := (collapsed i j k l hij hkl).1
  rw [← hijv,← hklv] at h
  have middle : u i ^ 4 = v k ^ 4 := by
    rcases h with he | ho
    · linear_combination (u i^2-v k^2)*he
    · have hz : u i*v k = 0 := by linear_combination ho/2
      exact ((mul_ne_zero (hu i) (hv k)) hz).elim
  have left : u 0 ^ 4 = u i ^ 4 := by
    calc
      u 0 ^ 4 = (u 0 ^ 2)^2 := by ring
      _ = (u i ^ 2)^2 := congrArg (fun z : K => z^2) (su 0 i)
      _ = u i ^ 4 := by ring
  have right : v k ^ 4 = v 0 ^ 4 := by
    calc
      v k ^ 4 = (v k ^ 2)^2 := by ring
      _ = (v 0 ^ 2)^2 := congrArg (fun z : K => z^2) (sv k 0)
      _ = v 0 ^ 4 := by ring
  exact left.trans (middle.trans right)

/-- Different anchors force one genuinely live E/O pair in one of the two
native incidence orientations. No vanished sector is promoted to hardness. -/
theorem live_pair [CharZero K] (u v : Fin 4 → K) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (different : u 0 ^ 4 ≠ v 0 ^ 4) :
    ∃ i j k l, i ≠ j ∧ k ≠ l ∧ u i*u j+v k*v l ≠ 0 ∧
      (u i*v k+u j*v l ≠ 0 ∨ u i*v l+u j*v k ≠ 0) := by
  classical
  by_contra missing
  have collapsed : Collapsed u v := by
    intro i j k l hij hkl
    by_cases he : u i*u j+v k*v l = 0
    · exact ⟨Or.inl he,Or.inl he⟩
    constructor
    · right
      by_contra ho
      exact missing ⟨i,j,k,l,hij,hkl,he,Or.inl ho⟩
    · right
      by_contra ho
      exact missing ⟨i,j,k,l,hij,hkl,he,Or.inr ho⟩
  exact different (fourth_anchor u v hu hv collapsed)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeMixedPairs
end
