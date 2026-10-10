import Holant.OpenNetworkComposition.FreeFree

/-! Remove a native wire ending at one exposed free stub and expose its original
ordinary opposite port. This preserves all vertices and their local port order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Normalize
open FiniteShape
variable {V F E : Type*} {n : ℕ}
variable (s : FiniteShape V F E n) (f : F) (i : Fin n)
    (p : Σ v,Fin (s.arity v)) (hi : s.boundary i=.inr f)
    (hp : s.ends ((s.freeEdge f).1,!(s.freeEdge f).2)=.inl p)

include hp in
theorem opposite_eq : s.cutOpposite f=.inl p := by
  apply (s.cutEmbed f).injective
  simpa using hp

include hp in
theorem old_boundary_ne (j : Fin n) : s.boundary j≠.inl p := by
  intro hj
  exact (s.ordinary_boundary_iff_unpaired p).mp ⟨j,hj⟩ ⟨_,hp⟩

def boundary : Fin n ↪ s.CutPorts f where
  toFun j := if hj : j=i then .inl p else s.cutPort f (s.boundary j) (s.boundary_ne_selected f i hi j hj)
  inj' := by
    intro j k h
    by_cases hj : j=i <;> by_cases hk : k=i
    · exact hj.trans hk.symm
    · simp only [dite_eq_left hj,dite_eq_right hk] at h
      have hh := congrArg (s.cutEmbed f) h
      simp only [cutEmbed_inl,cutEmbed_cutPort] at hh
      exact (old_boundary_ne s f p hp k hh.symm).elim
    · simp only [dite_eq_right hj,dite_eq_left hk] at h
      have hh := congrArg (s.cutEmbed f) h
      simp only [cutEmbed_inl,cutEmbed_cutPort] at hh
      exact (old_boundary_ne s f p hp j hh).elim
    · simp only [dite_eq_right hj,dite_eq_right hk] at h
      apply s.boundary.injective
      simpa using congrArg (s.cutEmbed f) h

@[simp] theorem boundary_at : boundary s f i p hi hp i=.inl p := by simp [boundary]

theorem boundary_away (j : Fin n) (hj : j≠i) :
    boundary s f i p hi hp j=s.cutBoundary f i hi ⟨j,hj⟩ := by
  simp [boundary,hj,FiniteShape.cutBoundary]

theorem boundary_range (q : Σ v,Fin (s.arity v)) :
    (∃j,boundary s f i p hi hp j=.inl q) ↔ (∃j,s.boundary j=.inl q) ∨ p=q := by
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j
      rw [boundary_at] at hj
      exact Or.inr (Sum.inl.inj hj)
    · left
      refine ⟨j,?_⟩
      rw [boundary_away s f i p hi hp j hji] at hj
      simpa using congrArg (s.cutEmbed f) hj
  · rintro (⟨j,hj⟩ | rfl)
    · have hji : j≠i := by intro hh; subst j; rw [hi] at hj; cases hj
      refine ⟨j,?_⟩
      rw [boundary_away s f i p hi hp j hji]
      apply (s.cutEmbed f).injective
      simpa using hj
    · exact ⟨i,boundary_at s f i p hi hp⟩

theorem ordinary_rule (q : Σ v,Fin (s.arity v)) :
    (∃j,boundary s f i p hi hp j=.inl q) ↔ ¬∃e,s.cutEnds f e=.inl q := by
  rw [boundary_range]
  constructor
  · rintro (h | rfl) ⟨e,he⟩
    · apply (s.ordinary_boundary_iff_unpaired q).mp h
      exact ⟨(e.1.val,e.2),by simpa using congrArg (s.cutEmbed f) he⟩
    · exact s.cutEnds_ne_opposite f e (he.trans (opposite_eq s f p hp).symm)
  · intro hn
    by_cases hpq : p=q
    · exact Or.inr hpq
    · left
      apply (s.ordinary_boundary_iff_unpaired q).mpr
      intro h
      have hh := (s.cut_paired_iff f (.inl q)).mp h
      rcases hh with hh | hh
      · exact hn hh
      · rw [opposite_eq s f p hp] at hh
        exact hpq (Sum.inl.inj hh)

theorem free_boundary (g : CutFree f) :
    boundary s f i p hi hp (s.freeBoundary g.val)=.inr g := by
  have hgi : s.freeBoundary g.val≠i := by
    intro h
    have hh := s.free_boundary g.val
    rw [h,hi] at hh
    exact g.property (Sum.inr.inj hh).symm
  rw [boundary_away s f i p hi hp _ hgi]
  apply (s.cutEmbed f).injective
  simpa using s.free_boundary g.val

include hp in
theorem free_paired_exists (g : CutFree f) : ∃e,s.cutEnds f e=.inr g := by
  have h := (s.cut_paired_iff f (.inr g)).mp ⟨s.freeEdge g.val,s.free_paired g.val⟩
  rcases h with h | h
  · exact h
  · rw [opposite_eq s f p hp] at h
    cases h

def shape : FiniteShape V (CutFree f) (s.CutEdge f) n where
  arity := s.arity
  boundary := boundary s f i p hi hp
  ends := s.cutEnds f
  ordinary_boundary_iff_unpaired := ordinary_rule s f i p hi hp
  freeBoundary := fun g => s.freeBoundary g.val
  free_boundary := free_boundary s f i p hi hp
  freeEdge := fun g => Classical.choose (free_paired_exists s f p hp g)
  free_paired := fun g => Classical.choose_spec (free_paired_exists s f p hp g)

end Holant.OpenNetworkComposition.ProjectiveContraction.Normalize
