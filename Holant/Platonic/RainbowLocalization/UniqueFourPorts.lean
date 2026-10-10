import Holant.Platonic.RainbowLocalization.LocalFourPorts

/-! Global uniqueness of the four-port matching disagreement. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant.Pauli.ExoticKlein MatchingCut
variable {P : Type*} [Fintype P] [DecidableEq P] {r₀ r₁ r₂ : ℕ}

def fourPorts (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂) (p : P) : Finset P :=
  {p,M₀.mate p,M₁.mate p,M₂.mate p}

theorem fourPorts_card (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀) (p : P) (hne : M₀.mate p ≠ M₁.mate p) :
    (fourPorts M₀ M₁ M₂ p).card = 4 := by
  obtain ⟨h₂₀,h₂₁,_⟩ := local_four_port_relations M₀ M₁ M₂ h₂ h₁ h₀ p hne
  simp [fourPorts, (M₀.mate_ne_self p).symm, (M₁.mate_ne_self p).symm,
    (M₂.mate_ne_self p).symm, hne, h₂₀.symm, h₂₁.symm]

theorem fourPorts_closed (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀) (p : P) (hne : M₀.mate p ≠ M₁.mate p) :
    (∀ q ∈ fourPorts M₀ M₁ M₂ p, M₀.mate q ∈ fourPorts M₀ M₁ M₂ p) ∧
    (∀ q ∈ fourPorts M₀ M₁ M₂ p, M₁.mate q ∈ fourPorts M₀ M₁ M₂ p) ∧
    (∀ q ∈ fourPorts M₀ M₁ M₂ p, M₂.mate q ∈ fourPorts M₀ M₁ M₂ p) := by
  obtain ⟨h₂₀,h₂₁,h20,h10,h01⟩ := local_four_port_relations M₀ M₁ M₂ h₂ h₁ h₀ p hne
  have h21 : M₂.mate (M₁.mate p) = M₀.mate p :=
    (congrArg M₂.mate h20).symm.trans (M₂.mate_mate _)
  have h12 : M₁.mate (M₂.mate p) = M₀.mate p :=
    (congrArg M₁.mate h10).symm.trans (M₁.mate_mate _)
  have h02 : M₀.mate (M₂.mate p) = M₁.mate p :=
    (congrArg M₀.mate h01).symm.trans (M₀.mate_mate _)
  constructor
  · intro q hq
    simp only [fourPorts,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq <;> subst q <;> simp [fourPorts,h01,h02]
  constructor
  · intro q hq
    simp only [fourPorts,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq <;> subst q <;> simp [fourPorts,h10,h12]
  · intro q hq
    simp only [fourPorts,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq <;> subst q <;> simp [fourPorts,h20,h21]

private theorem complement_closed {r : ℕ} (M : Matching P r) (S : Finset P)
    (hS : ∀ p ∈ S, M.mate p ∈ S) : ∀ p, p ∉ S → M.mate p ∉ S := by
  intro p hp hm
  exact hp (by simpa using hS (M.mate p) hm)

private theorem crossing_four_le_two_of_internal {r : ℕ} (M : Matching P r) (S : Finset P)
    (hcard : S.card = 4) (hi : HasInternalEdge M S) :
    Fintype.card (Crossing M (cut S)) ≤ 2 := by
  have he := cut_card M S
  have hp : 0 < Fintype.card (Internal M (cut S) true) :=
    Fintype.card_pos_iff.mpr ((internal_nonempty_iff M S).mpr hi)
  omega

/-- Two disjoint exceptional blocks would produce a four-port cut with
crossing counts at most two, at most two, and exactly four. -/
theorem agreement_outside_fourPorts
    (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀) (p : P) (hne : M₀.mate p ≠ M₁.mate p)
    (q : P) (hq : q ∉ fourPorts M₀ M₁ M₂ p) : M₀.mate q = M₁.mate q := by
  by_contra hneq
  let S := fourPorts M₀ M₁ M₂ p
  let T := fourPorts M₀ M₁ M₂ q
  let U : Finset P := {p,M₀.mate p,q,M₁.mate q}
  obtain ⟨hp₂₀,hp₂₁,hp20,hp10,hp01⟩ := local_four_port_relations M₀ M₁ M₂ h₂ h₁ h₀ p hne
  obtain ⟨hq₂₀,hq₂₁,hq20,hq10,hq01⟩ := local_four_port_relations M₀ M₁ M₂ h₂ h₁ h₀ q hneq
  obtain ⟨hc₀,hc₁,hc₂⟩ := fourPorts_closed M₀ M₁ M₂ h₂ h₁ h₀ p hne
  have hq₀ := complement_closed M₀ S hc₀ q hq
  have hq₁ := complement_closed M₁ S hc₁ q hq
  have hq₂ := complement_closed M₂ S hc₂ q hq
  have hdis : ∀ z ∈ T, z ∉ S := by
    intro z hz
    simp only [T,fourPorts,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz <;> subst z <;> assumption
  have hcross (x y : P) (hx : x ∈ S) (hy : y ∈ T) : x ≠ y := by
    intro he
    exact hdis y hy (he ▸ hx)
  have hpS : p ∈ S := by simp [S,fourPorts]
  have hp₀S : M₀.mate p ∈ S := by simp [S,fourPorts]
  have hqT : q ∈ T := by simp [T,fourPorts]
  have hq₁T : M₁.mate q ∈ T := by simp [T,fourPorts]
  have hcard : U.card = 4 := by
    simp [U,(M₀.mate_ne_self p).symm,(M₁.mate_ne_self q).symm,
      hcross p q hpS hqT,hcross p (M₁.mate q) hpS hq₁T,
      hcross (M₀.mate p) q hp₀S hqT,hcross (M₀.mate p) (M₁.mate q) hp₀S hq₁T]
  have hSnot (x : P) (hx : x ∈ S) (hp : x ≠ p) (hp₀ : x ≠ M₀.mate p) : x ∉ U := by
    simp only [U,Finset.mem_insert,Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact hp h
    · exact hp₀ h
    · exact hcross x q hx hqT h
    · exact hcross x (M₁.mate q) hx hq₁T h
  have hTnot (x : P) (hx : x ∈ T) (hqx : x ≠ q) (hq₁ : x ≠ M₁.mate q) : x ∉ U := by
    simp only [U,Finset.mem_insert,Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact hcross p x hpS hx h.symm
    · exact hcross (M₀.mate p) x hp₀S hx h.symm
    · exact hqx h
    · exact hq₁ h
  have hq21 : M₂.mate (M₁.mate q) = M₀.mate q :=
    (congrArg M₂.mate hq20).symm.trans (M₂.mate_mate _)
  have hno : ¬ HasInternalEdge M₂ U := by
    rintro ⟨x,hx,hm⟩
    simp only [U,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x
    · exact hSnot _ (by simp [S,fourPorts]) (M₂.mate_ne_self p) hp₂₀ hm
    · rw [hp20] at hm
      exact hSnot _ (by simp [S,fourPorts]) (M₁.mate_ne_self p) hne.symm hm
    · exact hTnot _ (by simp [T,fourPorts]) (M₂.mate_ne_self q) hq₂₁ hm
    · rw [hq21] at hm
      exact hTnot _ (by simp [T,fourPorts]) (M₀.mate_ne_self q) hneq hm
  have hi₀ : HasInternalEdge M₀ U := ⟨p,by simp [U],by simp [U]⟩
  have hi₁ : HasInternalEdge M₁ U := ⟨q,by simp [U],by simp [U]⟩
  have hc₀ := crossing_four_le_two_of_internal M₀ U hcard hi₀
  have hc₁ := crossing_four_le_two_of_internal M₁ U hcard hi₁
  have hp₀ : 2 ^ Fintype.card (Crossing M₀ (cut U)) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hc₀
  have hp₁ : 2 ^ Fintype.card (Crossing M₁ (cut U)) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hc₁
  have hh := h₂ U
  rw [crossing_eq_card_of_no_internal M₂ U hno,hcard] at hh
  norm_num at hp₀ hp₁ hh
  omega

/-- The three given matchings have a common four-port invariant set and
agree everywhere outside that set. -/
theorem exists_four_port_disagreement
    (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀) (hne : M₀.mate ≠ M₁.mate) :
    ∃ S : Finset P, S.card = 4 ∧
      (∀ q ∈ S, M₀.mate q ∈ S) ∧ (∀ q ∈ S, M₁.mate q ∈ S) ∧
      (∀ q ∈ S, M₂.mate q ∈ S) ∧
      ∀ q, q ∉ S → M₀.mate q = M₁.mate q ∧ M₂.mate q = M₀.mate q := by
  have hex : ∃ p, M₀.mate p ≠ M₁.mate p := by
    by_contra hh
    push Not at hh
    exact hne (Equiv.ext hh)
  obtain ⟨p,hp⟩ := hex
  obtain ⟨hc₀,hc₁,hc₂⟩ := fourPorts_closed M₀ M₁ M₂ h₂ h₁ h₀ p hp
  refine ⟨fourPorts M₀ M₁ M₂ p,fourPorts_card M₀ M₁ M₂ h₂ h₁ h₀ p hp,hc₀,hc₁,hc₂,?_⟩
  intro q hq
  have he := agreement_outside_fourPorts M₀ M₁ M₂ h₂ h₁ h₀ p hp q hq
  exact ⟨he,edge_of_two M₀ M₁ M₂ h₂ q (M₀.mate q) rfl he.symm⟩

theorem fourPorts_disagreement_iff
    (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀) (p : P) (hne : M₀.mate p ≠ M₁.mate p)
    (q : P) : q ∈ fourPorts M₀ M₁ M₂ p ↔ M₀.mate q ≠ M₁.mate q := by
  constructor
  · intro hq
    obtain ⟨h₂₀,h₂₁,h20,h10,h01⟩ := local_four_port_relations M₀ M₁ M₂ h₂ h₁ h₀ p hne
    have h12 : M₁.mate (M₂.mate p) = M₀.mate p :=
      (congrArg M₁.mate h10).symm.trans (M₁.mate_mate _)
    have h02 : M₀.mate (M₂.mate p) = M₁.mate p :=
      (congrArg M₀.mate h01).symm.trans (M₀.mate_mate _)
    simp only [fourPorts,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq <;> subst q
    · exact hne
    · simpa only [M₀.mate_mate,h10] using (M₂.mate_ne_self p).symm
    · simpa only [h01,M₁.mate_mate] using M₂.mate_ne_self p
    · simpa only [h02,h12] using hne.symm
  · intro hq
    by_contra hn
    exact hq (agreement_outside_fourPorts M₀ M₁ M₂ h₂ h₁ h₀ p hne q hn)

/-- The exceptional set is uniquely determined by the actual matchings.
Its membership is exactly where the first two mates disagree. -/
theorem unique_four_port_disagreement
    (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀) (hne : M₀.mate ≠ M₁.mate) :
    ∃! S : Finset P, S.card = 4 ∧ ∀ q, q ∈ S ↔ M₀.mate q ≠ M₁.mate q := by
  have hex : ∃ p, M₀.mate p ≠ M₁.mate p := by
    by_contra hh
    push Not at hh
    exact hne (Equiv.ext hh)
  obtain ⟨p,hp⟩ := hex
  refine ⟨fourPorts M₀ M₁ M₂ p,
    ⟨fourPorts_card M₀ M₁ M₂ h₂ h₁ h₀ p hp,
      fourPorts_disagreement_iff M₀ M₁ M₂ h₂ h₁ h₀ p hp⟩,?_⟩
  intro T hT
  ext q
  rw [hT.2 q,fourPorts_disagreement_iff M₀ M₁ M₂ h₂ h₁ h₀ p hp q]

end Holant.Platonic.RainbowLocalization
