import Holant.OpenNetworkComposition.OrdinaryPorts
import Mathlib.Tactic.FinCases

/-! A complete valid OpenNetwork incidence constructor for the disjoint
ordinary/ordinary boundary case; no new vertex or resource is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.Ordinary
variable {VL VR FL FR EL ER : Type*} {n : ℕ}
variable (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2) (i : Fin n)

theorem endpoint_range_left (p : Ports VL FL L.arity) :
    (∃ e,endpoint L R i e=leftPort L.arity R.arity p) ↔
      (∃ e,L.ends e=p) ∨ L.boundary i=p := by
  constructor
  · rintro ⟨⟨((e | e) | u),b⟩,h⟩
    · exact Or.inl ⟨(e,b),(leftPort L.arity R.arity).injective h⟩
    · exact (right_left_ne _ _ _ _ h).elim
    · cases b
      · exact Or.inr ((leftPort L.arity R.arity).injective h)
      · exact (right_left_ne _ _ _ _ h).elim
  · rintro (⟨e,h⟩ | h)
    · exact ⟨(.inl (.inl e.1),e.2),congrArg (leftPort L.arity R.arity) h⟩
    · exact ⟨(.inr (),false),congrArg (leftPort L.arity R.arity) h⟩

theorem endpoint_range_right (p : Ports VR FR R.arity) :
    (∃ e,endpoint L R i e=rightPort L.arity R.arity p) ↔
      (∃ e,R.ends e=p) ∨ R.boundary 1=p := by
  constructor
  · rintro ⟨⟨((e | e) | u),b⟩,h⟩
    · exact (left_right_ne _ _ _ _ h).elim
    · exact Or.inl ⟨(e,b),(rightPort L.arity R.arity).injective h⟩
    · cases b
      · exact (left_right_ne _ _ _ _ h).elim
      · exact Or.inr ((rightPort L.arity R.arity).injective h)
  · rintro (⟨e,h⟩ | h)
    · exact ⟨(.inl (.inr e.1),e.2),congrArg (rightPort L.arity R.arity) h⟩
    · exact ⟨(.inr (),true),congrArg (rightPort L.arity R.arity) h⟩

theorem boundary_range_left (p : Ports VL FL L.arity) :
    (∃ j,boundary L R i j=leftPort L.arity R.arity p) ↔
      ∃ j,j≠i ∧ L.boundary j=p := by
  constructor
  · rintro ⟨j,h⟩
    change (if j=i then rightPort L.arity R.arity (R.boundary 0) else leftPort L.arity R.arity (L.boundary j))=_ at h
    by_cases hj : j=i
    · simp only [hj,ite_true] at h
      exact (right_left_ne _ _ _ _ h).elim
    · simp only [hj,ite_false] at h
      exact ⟨j,hj,(leftPort L.arity R.arity).injective h⟩
  · rintro ⟨j,hj,h⟩
    refine ⟨j,?_⟩
    change (if j=i then rightPort L.arity R.arity (R.boundary 0) else leftPort L.arity R.arity (L.boundary j))=_
    simp only [hj,ite_false]
    exact congrArg (leftPort L.arity R.arity) h

theorem boundary_range_right (p : Ports VR FR R.arity) :
    (∃ j,boundary L R i j=rightPort L.arity R.arity p) ↔ R.boundary 0=p := by
  constructor
  · rintro ⟨j,h⟩
    change (if j=i then rightPort L.arity R.arity (R.boundary 0) else leftPort L.arity R.arity (L.boundary j))=_ at h
    by_cases hj : j=i
    · simp only [hj,ite_true] at h
      exact (rightPort L.arity R.arity).injective h
    · simp only [hj,ite_false] at h
      exact (left_right_ne _ _ _ _ h).elim
  · intro h
    refine ⟨i,?_⟩
    change (if i=i then rightPort L.arity R.arity (R.boundary 0) else leftPort L.arity R.arity (L.boundary i))=_
    rw [if_pos rfl]
    exact congrArg (rightPort L.arity R.arity) h

theorem ordinary_left (p : Σ v : VL,Fin (L.arity v)) :
    (∃ j,boundary L R i j=leftPort L.arity R.arity (.inl p)) ↔
      ¬∃ e,endpoint L R i e=leftPort L.arity R.arity (.inl p) := by
  rw [boundary_range_left,endpoint_range_left]
  constructor
  · rintro ⟨j,hj,hp⟩ (he | hi)
    · exact (L.ordinary_boundary_iff_unpaired p).mp ⟨j,hp⟩ he
    · exact hj (L.boundary.injective (hp.trans hi.symm))
  · intro h
    obtain ⟨j,hj⟩ := (L.ordinary_boundary_iff_unpaired p).mpr (fun he => h (Or.inl he))
    exact ⟨j,fun hi => h (Or.inr (hi ▸ hj)),hj⟩

theorem ordinary_right (p : Σ v : VR,Fin (R.arity v)) :
    (∃ j,boundary L R i j=rightPort L.arity R.arity (.inl p)) ↔
      ¬∃ e,endpoint L R i e=rightPort L.arity R.arity (.inl p) := by
  rw [boundary_range_right,endpoint_range_right]
  constructor
  · intro h
    rintro (he | hi)
    · exact (R.ordinary_boundary_iff_unpaired p).mp ⟨0,h⟩ he
    · have hh := R.boundary.injective (h.trans hi.symm)
      exact (by decide : (0 : Fin 2)≠1) hh
  · intro h
    obtain ⟨j,hj⟩ := (R.ordinary_boundary_iff_unpaired p).mpr (fun he => h (Or.inl he))
    fin_cases j
    · exact hj
    · exact (h (Or.inr hj)).elim

variable (pL : Σ v : VL,Fin (L.arity v)) (pR : Σ v : VR,Fin (R.arity v))
variable (hL : L.boundary i=Sum.inl pL) (hR : R.boundary 1=Sum.inl pR)

include hL in
theorem left_free_ne (f : FL) : L.freeBoundary f≠i := by
  intro h
  have hh := L.free_boundary f
  rw [h,hL] at hh
  cases hh

include hR in
theorem right_free_zero (f : FR) : R.freeBoundary f=0 := by
  have hn : R.freeBoundary f≠1 := by
    intro h
    have hh := R.free_boundary f
    rw [h,hR] at hh
    cases hh
  have hb := (R.freeBoundary f).isLt
  apply Fin.ext
  have hn' : (R.freeBoundary f).val≠1 := by
    intro h
    apply hn
    exact Fin.ext h
  omega

/-- The new shape is valid for arbitrary scalar components and untouched free
stubs; only the two selected ordinary boundary occurrences are paired. -/
abbrev shape : FiniteShape (VL ⊕ VR) (FL ⊕ FR) ((EL ⊕ ER) ⊕ Unit) n where
  arity := SumArity L.arity R.arity
  boundary := boundary L R i
  ends := ends L R i pL pR hL hR
  ordinary_boundary_iff_unpaired := by
    rintro ⟨(v | v),j⟩
    · exact ordinary_left L R i ⟨v,j⟩
    · exact ordinary_right L R i ⟨v,j⟩
  freeBoundary := Sum.elim L.freeBoundary (fun _ => i)
  free_boundary := by
    rintro (f | f)
    · change (if L.freeBoundary f=i then _ else _)=_
      rw [if_neg (left_free_ne L i pL hL f)]
      change leftPort L.arity R.arity (L.boundary (L.freeBoundary f))=_
      rw [L.free_boundary]
      rfl
    · change (if i=i then _ else _)=_
      rw [if_pos rfl,← right_free_zero R pR hR f,R.free_boundary]
      rfl
  freeEdge := Sum.elim
    (fun f => (.inl (.inl (L.freeEdge f).1),(L.freeEdge f).2))
    (fun f => (.inl (.inr (R.freeEdge f).1),(R.freeEdge f).2))
  free_paired := by
    rintro (f | f)
    · change leftPort L.arity R.arity (L.ends (L.freeEdge f))=_
      rw [L.free_paired]
      rfl
    · change rightPort L.arity R.arity (R.ends (R.freeEdge f))=_
      rw [R.free_paired]
      rfl

end Holant.OpenNetworkComposition.Ordinary
