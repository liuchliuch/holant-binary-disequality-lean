import Holant.ReedMuller.AffineRadon.SpaceGeometry

/-! Avoidance of two proper binary subspaces, with the all-one exception
removed by actual dimension rather than an assumed accessible witness. -/
namespace Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem exists_outside_two_subspaces (W U V : BinaryCode n)
    (hU : ¬ W ≤ U) (hV : ¬ W ≤ V) :
    ∃ x : BinaryVector n, x ∈ W ∧ x ∉ U ∧ x ∉ V := by
  by_contra! h
  have hcover : (W : Set (BinaryVector n)) ⊆ (U : Set (BinaryVector n)) ∪ V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr (h x hx hxU)
  exact (AddSubgroupClass.subset_union.mp hcover).elim hU hV

/-- A two-dimension gap permits simultaneously avoiding a target subspace
and the line containing the excluded all-one word. -/
theorem exists_accessible_outside_subspace (W U : BinaryCode n)
    (heven : W ≤ evenSpace n)
    (hdim : Module.finrank (ZMod 2) U + 2 ≤ Module.finrank (ZMod 2) W) :
    ∃ v : BinaryVector n, v ∈ W ∧ Accessible v ∧ v ∉ U := by
  let T := U ⊔ Submodule.span (ZMod 2) {ones n}
  have ht : Module.finrank (ZMod 2) T ≤ Module.finrank (ZMod 2) U + 1 := by
    have hl : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {ones n}) ≤ 1 := by
      simpa using finrank_span_le_card (R := ZMod 2) ({ones n} : Set (BinaryVector n))
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left hl _)
  have hn : ¬ W ≤ T := by
    intro h
    have hh := (Submodule.finrank_mono h).trans ht
    omega
  obtain ⟨v, hv, hvn⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨v, hv, ⟨heven hv, ?_, ?_⟩, ?_⟩
  · intro h; subst v; exact hvn T.zero_mem
  · intro h; subst v
    exact hvn (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
  · intro h
    exact hvn (Submodule.mem_sup_left h)

/-- In dimension at least three the complement of two proper subspaces
cannot consist of a single exceptional vector. -/
theorem exists_outside_two_subspaces_ne (W U V : BinaryCode n)
    (hdim : 3 ≤ Module.finrank (ZMod 2) W)
    (hU : ¬ W ≤ U) (hV : ¬ W ≤ V) (c : BinaryVector n) :
    ∃ x : BinaryVector n, x ∈ W ∧ x ∉ U ∧ x ∉ V ∧ x ≠ c := by
  by_contra! h
  obtain ⟨z, hz, hzU, hzV⟩ := exists_outside_two_subspaces W U V hU hV
  have hzc : z = c := h z hz hzU hzV
  subst z
  have hcover : ∀ x, x ∈ W → x ≠ c → x ∈ U ∨ x ∈ V := by
    intro x hx hxc
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · right
      by_contra hxV
      exact hxc (h x hx hxU hxV)
  have hline : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {c}) ≤ 1 := by
    simpa using finrank_span_le_card (R := ZMod 2) ({c} : Set (BinaryVector n))
  have hnot : ¬ W ≤ Submodule.span (ZMod 2) {c} := by
    intro hh
    have hh' := (Submodule.finrank_mono hh).trans hline
    omega
  obtain ⟨p, hp, hpn⟩ := SetLike.not_le_iff_exists.mp hnot
  let T : BinaryCode n := Submodule.span (ZMod 2) {c,p}
  have hTdim : Module.finrank (ZMod 2) T ≤ 2 := by
    have hh := finrank_span_le_card (R := ZMod 2) ({c,p} : Set (BinaryVector n))
    have hc : ({c,p} : Set (BinaryVector n)).toFinset = ({c,p} : Finset (BinaryVector n)) := by ext x; simp
    rw [hc] at hh
    exact hh.trans Finset.card_le_two
  have hnotT : ¬ W ≤ T := by
    intro hh
    have hh' := (Submodule.finrank_mono hh).trans hTdim
    omega
  obtain ⟨w, hw, hwn⟩ := SetLike.not_le_iff_exists.mp hnotT
  have hcT : c ∈ T := Submodule.subset_span (by simp)
  have hpT : p ∈ T := Submodule.subset_span (by simp)
  have hp0 : p ≠ 0 := by intro hh; subst p; exact hpn (Submodule.zero_mem _)
  have hpc : p ≠ c := by
    intro hh; subst p; exact hpn (Submodule.subset_span (Set.mem_singleton _))
  have hw0 : w ≠ 0 := by intro hh; subst w; exact hwn T.zero_mem
  have hwc : w ≠ c := by intro hh; subst w; exact hwn hcT
  have hcw : c + w ≠ c := by
    intro hh
    exact hw0 (add_left_cancel (show c+w=c+0 by simpa using hh))
  have hqw : c-p+w ≠ c := by
    intro hh
    have heq : w = c-(c-p) := by
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using hh
    exact hwn (heq ▸ T.sub_mem hcT (T.sub_mem hcT hpT))
  have hpw : p+w ≠ c := by
    intro hh
    have heq : w = c-p := by
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using hh
    exact hwn (heq ▸ T.sub_mem hcT hpT)
  have hcpmem : c-p ∈ W := W.sub_mem hz hp
  have hcpc : c-p ≠ c := by
    intro hh
    have heq := sub_eq_iff_eq_add.mp hh
    exact hp0 (add_left_cancel (show c+p=c+0 by simpa using heq.symm))
  have hinter : ∀ x, x ∈ W → x ≠ 0 → x ∈ U → x ∈ V → False := by
    intro x hx hx0 hxU hxV
    have hn : c+x ≠ c := by
      intro hh
      exact hx0 (add_left_cancel (show c+x=c+0 by simpa using hh))
    rcases hcover (c+x) (W.add_mem hz hx) hn with hh | hh
    · exact hzU (by simpa using U.sub_mem hh hxU)
    · exact hzV (by simpa using V.sub_mem hh hxV)
  rcases hcover p hp hpc with hpU | hpV
  · have hpV : p ∉ V := fun hh => hinter p hp hp0 hpU hh
    have hqU : c-p ∉ U := by
      intro hh
      exact hzU (by simpa using U.add_mem hh hpU)
    have hqV : c-p ∈ V := (hcover (c-p) hcpmem hcpc).resolve_left hqU
    rcases hcover w hw hwc with hwU | hwV
    · rcases hcover (c-p+w) (W.add_mem hcpmem hw) hqw with hh | hh
      · exact hqU (by simpa using U.sub_mem hh hwU)
      · exact hinter w hw hw0 hwU (by simpa using V.sub_mem hh hqV)
    · rcases hcover (p+w) (W.add_mem hp hw) hpw with hh | hh
      · exact hinter w hw hw0 (by simpa using U.sub_mem hh hpU) hwV
      · exact hpV (by simpa using V.sub_mem hh hwV)
  · have hpU : p ∉ U := fun hh => hinter p hp hp0 hh hpV
    have hqV : c-p ∉ V := by
      intro hh
      exact hzV (by simpa using V.add_mem hh hpV)
    have hqU : c-p ∈ U := (hcover (c-p) hcpmem hcpc).resolve_right hqV
    rcases hcover w hw hwc with hwU | hwV
    · rcases hcover (p+w) (W.add_mem hp hw) hpw with hh | hh
      · exact hpU (by simpa using U.sub_mem hh hwU)
      · exact hinter w hw hw0 hwU (by simpa using V.sub_mem hh hpV)
    · rcases hcover (c-p+w) (W.add_mem hcpmem hw) hqw with hh | hh
      · exact hinter w hw hw0 (by simpa using U.sub_mem hh hqU) hwV
      · exact hqV (by simpa using V.sub_mem hh hwV)

/-- The accessible direction used to force support dimension `r` in 7.19. -/
theorem exists_accessible_outside_union {r : ℕ} (hr : 4 ≤ r)
    (U V : BinaryCode (2*r))
    (hU : ¬ evenSpace (2*r) ≤ U) (hV : ¬ evenSpace (2*r) ≤ V) :
    ∃ v : BinaryVector (2*r), Accessible v ∧ v ∉ U ∧ v ∉ V := by
  have hd : 3 ≤ Module.finrank (ZMod 2) (evenSpace (2*r)) := by
    rw [finrank_evenSpace (by omega : 0 < 2*r)]
    omega
  obtain ⟨v, hv, hvU, hvV, hv1⟩ :=
    exists_outside_two_subspaces_ne (evenSpace (2*r)) U V hd hU hV (ones (2*r))
  exact ⟨v, ⟨hv, by intro hh; subst v; exact hvU U.zero_mem, hv1⟩, hvU, hvV⟩

end
end Holant.ReedMuller.AffineRadon
