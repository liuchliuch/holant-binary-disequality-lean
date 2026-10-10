import Holant.ReedMuller.MatchingConsistency.Pairing

/-! Local unions of two optional perfect pairings force a matching globally.
The pairings may disagree: their exclusive edges are required to occur in
`W`, and every edge of `W` must occur in their union. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.ZeroCardGraph

variable {ι : Type*}

/-- The absent pairing represents a zero card. -/
def optionalAdj (M : Option (Pairing ι)) (u v : ι) : Prop :=
  ∃ P, M = some P ∧ P.mate u = v

@[simp] theorem optionalAdj_none (u v : ι) : ¬ optionalAdj none u v := by
  rintro ⟨P, h, _⟩
  cases h

@[simp] theorem optionalAdj_some (P : Pairing ι) (u v : ι) :
    optionalAdj (some P) u v ↔ P.mate u = v := by
  simp [optionalAdj]

theorem optionalAdj_symm {M : Option (Pairing ι)} {u v : ι}
    (h : optionalAdj M u v) : optionalAdj M v u := by
  rcases h with ⟨P, rfl, h⟩
  exact ⟨P, rfl, (P.mate_eq_iff _ _).mp h⟩

theorem optionalAdj_unique {M : Option (Pairing ι)} {u v w : ι}
    (hv : optionalAdj M u v) (hw : optionalAdj M u w) : v = w := by
  rcases hv with ⟨P, rfl, hv⟩
  rw [optionalAdj_some] at hw
  exact hv.symm.trans hw

/-- No agreement between the two card pairings is assumed. -/
structure LocalCover (W : SimpleGraph ι) (i j : ι) where
  left : Option (Pairing (Remaining i j))
  right : Option (Pairing (Remaining i j))
  cover : ∀ u v, W.Adj u.val v.val → optionalAdj left u v ∨ optionalAdj right u v
  left_only : ∀ u v, optionalAdj left u v → ¬ optionalAdj right u v → W.Adj u.val v.val
  right_only : ∀ u v, optionalAdj right u v → ¬ optionalAdj left u v → W.Adj u.val v.val

def LocalCover.swap {W : SimpleGraph ι} {i j : ι} (C : LocalCover W i j) :
    LocalCover W i j where
  left := C.right
  right := C.left
  cover u v h := (C.cover u v h).symm
  left_only := C.right_only
  right_only := C.left_only

private theorem optionalAdj_three {P Q : Option (Pairing ι)} {u v w x : ι}
    (hv : optionalAdj P u v ∨ optionalAdj Q u v)
    (hw : optionalAdj P u w ∨ optionalAdj Q u w)
    (hx : optionalAdj P u x ∨ optionalAdj Q u x) :
    v = w ∨ v = x ∨ w = x := by
  rcases hv with hv | hv <;> rcases hw with hw | hw <;> rcases hx with hx | hx
  all_goals first
    | exact Or.inl (optionalAdj_unique hv hw)
    | exact Or.inr (Or.inl (optionalAdj_unique hv hx))
    | exact Or.inr (Or.inr (optionalAdj_unique hw hx))

private theorem LocalCover.extend_oriented {W : SimpleGraph ι} {i j : ι}
    (C : LocalCover W i j) (u v w : Remaining i j)
    (huv : W.Adj u.val v.val) (hvw : v ≠ w)
    (hleft : optionalAdj C.left u v) (hright : optionalAdj C.right u w) :
    ∃ k : Remaining i j, W.Adj v.val k.val ∧ k ≠ u ∧ k ≠ v ∧ k ≠ w := by
  rcases hright with ⟨P, hP, hPw⟩
  let k : Remaining i j := P.mate v
  have hvk : optionalAdj C.right v k := ⟨P, hP, rfl⟩
  have hku : k ≠ u := by
    intro h
    have hvu : P.mate v = u := h
    have huv' : P.mate u = v := (P.mate_eq_iff _ _).mp hvu
    exact hvw (huv'.symm.trans hPw)
  have hkv : k ≠ v := P.ne_self v
  have hkw : k ≠ w := by
    intro h
    have hvu : v = u := P.injective (h.trans hPw.symm)
    exact huv.ne (congrArg Subtype.val hvu.symm)
  refine ⟨k, C.right_only v k hvk ?_, hku, hkv, hkw⟩
  intro hleft'
  exact hku (optionalAdj_unique hleft' (optionalAdj_symm hleft))

/-- A retained two-edge star forces a new edge at either of its leaves. -/
theorem LocalCover.star_extension {W : SimpleGraph ι} {i j : ι}
    (C : LocalCover W i j) (u v w : Remaining i j)
    (huv : W.Adj u.val v.val) (huw : W.Adj u.val w.val) (hvw : v ≠ w) :
    ∃ k : Remaining i j, W.Adj v.val k.val ∧ k ≠ u ∧ k ≠ v ∧ k ≠ w := by
  rcases C.cover u v huv with hl | hr
  · rcases C.cover u w huw with hl' | hr'
    · exact False.elim (hvw (optionalAdj_unique hl hl'))
    · exact C.extend_oriented u v w huv hvw hl hr'
  · rcases C.cover u w huw with hl' | hr'
    · exact C.swap.extend_oriented u v w huv hvw hr hl'
    · exact False.elim (hvw (optionalAdj_unique hr hr'))

private theorem exists_two_outside [Fintype ι] [DecidableEq ι]
    (hcard : 6 ≤ Fintype.card ι) (s : Finset ι) (hs : s.card ≤ 4) :
    ∃ i j : ι, i ≠ j ∧ ∀ x ∈ s, x ≠ i ∧ x ≠ j := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card < (Finset.univ : Finset ι).card by simpa using (by omega : s.card < Fintype.card ι))
  have hins := Finset.card_insert_le i s
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (insert i s).card < (Finset.univ : Finset ι).card by
      simpa using (by omega : (insert i s).card < Fintype.card ι))
  have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self i s)
  have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
  refine ⟨i, j, hji.symm, ?_⟩
  intro x hx
  exact ⟨fun h => hi (h ▸ hx), fun h => hjs (h ▸ hx)⟩

/-- The union bound first rules out three distinct global neighbors. -/
theorem localCover_degree_le_two [Fintype ι] [DecidableEq ι]
    (W : SimpleGraph ι) (hcard : 6 ≤ Fintype.card ι)
    (hlocal : ∀ i j, i ≠ j → Nonempty (LocalCover W i j))
    (u v w x : ι) (hv : W.Adj u v) (hw : W.Adj u w) (hx : W.Adj u x) :
    v = w ∨ v = x ∨ w = x := by
  obtain ⟨i, j, hij, hout⟩ := exists_two_outside hcard {u, v, w, x} Finset.card_le_four
  let u' : Remaining i j := ⟨u, hout u (by simp)⟩
  let v' : Remaining i j := ⟨v, hout v (by simp)⟩
  let w' : Remaining i j := ⟨w, hout w (by simp)⟩
  let x' : Remaining i j := ⟨x, hout x (by simp)⟩
  obtain ⟨C⟩ := hlocal i j hij
  rcases optionalAdj_three (C.cover u' v' hv) (C.cover u' w' hw)
    (C.cover u' x' hx) with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (congrArg Subtype.val h))

/-- Six original ports suffice: deleting the forced extra neighbor contradicts
its uniqueness under the global degree-two bound. -/
theorem localCover_degree_le_one [Fintype ι] [DecidableEq ι]
    (W : SimpleGraph ι) (hcard : 6 ≤ Fintype.card ι)
    (hlocal : ∀ i j, i ≠ j → Nonempty (LocalCover W i j)) :
    ∀ u v w, W.Adj u v → W.Adj u w → v = w := by
  intro u v w huv huw
  by_contra hvw
  obtain ⟨i, j, hij, hout⟩ := exists_two_outside hcard {u, v, w} (Finset.card_le_three.trans (by omega))
  let u' : Remaining i j := ⟨u, hout u (by simp)⟩
  let v' : Remaining i j := ⟨v, hout v (by simp)⟩
  let w' : Remaining i j := ⟨w, hout w (by simp)⟩
  obtain ⟨C⟩ := hlocal i j hij
  obtain ⟨k, hvk, hku, hkv, hkw⟩ :=
    C.star_extension u' v' w' huv huw (fun h => hvw (congrArg Subtype.val h))
  have hku' : k.val ≠ u := fun h => hku (Subtype.ext h)
  have hkv' : k.val ≠ v := fun h => hkv (Subtype.ext h)
  have hkw' : k.val ≠ w := fun h => hkw (Subtype.ext h)
  obtain ⟨a, b, hab, hout'⟩ := exists_two_outside hcard {u, v, w, k.val} Finset.card_le_four
  have hka : k.val ≠ a := (hout' k.val (by simp)).1
  let u'' : Remaining k.val a := ⟨u, hku'.symm, (hout' u (by simp)).1⟩
  let v'' : Remaining k.val a := ⟨v, hkv'.symm, (hout' v (by simp)).1⟩
  let w'' : Remaining k.val a := ⟨w, hkw'.symm, (hout' w (by simp)).1⟩
  obtain ⟨D⟩ := hlocal k.val a hka
  obtain ⟨l, hvl, hlu, _, _⟩ :=
    D.star_extension u'' v'' w'' huv huw (fun h => hvw (congrArg Subtype.val h))
  have hlu' : l.val ≠ u := fun h => hlu (Subtype.ext h)
  rcases localCover_degree_le_two W hcard hlocal v u k.val l.val huv.symm hvk hvl with
    h | h | h
  · exact hku' h.symm
  · exact hlu' h.symm
  · exact l.property.1 h.symm

end Holant.ReedMuller.MatchingConsistency
