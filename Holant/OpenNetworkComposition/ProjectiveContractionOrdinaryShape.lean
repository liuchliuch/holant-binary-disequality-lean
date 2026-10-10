import Holant.OpenNetworkComposition.Finite

/-! Close the first two ordinary boundaries of one actual open network. All
vertices, free stubs and old edges are retained; one native edge is inserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Ordinary
variable {V F E : Type*} {n : ℕ}
variable (s : FiniteShape V F E (n+2))
    (p0 p1 : Σ v,Fin (s.arity v)) (h0 : s.boundary 0=.inl p0) (h1 : s.boundary 1=.inl p1)

def boundary : Fin n ↪ Ports V F s.arity where
  toFun j := s.boundary j.succ.succ
  inj' := by
    intro a b h
    simpa using s.boundary.injective h

def endFn : (E ⊕ Unit) × Bool → Ports V F s.arity
  | (.inl e,b) => s.ends (e,b)
  | (.inr _,false) => s.boundary 0
  | (.inr _,true) => s.boundary 1

include h0 in
theorem first_not_end (e : E × Bool) : s.boundary 0≠s.ends e := by
  intro h
  exact (s.ordinary_boundary_iff_unpaired p0).mp ⟨0,h0⟩ ⟨e,h.symm.trans h0⟩
include h1 in
theorem second_not_end (e : E × Bool) : s.boundary 1≠s.ends e := by
  intro h
  exact (s.ordinary_boundary_iff_unpaired p1).mp ⟨1,h1⟩ ⟨e,h.symm.trans h1⟩

def ends : ((E ⊕ Unit) × Bool) ↪ Ports V F s.arity where
  toFun := endFn s
  inj' := by
    rintro ⟨(e|u),b⟩ ⟨(e'|u'),b'⟩ h
    · have hh := s.ends.injective h
      cases hh
      rfl
    · cases b'
      · exact (first_not_end s p0 h0 (e,b) h.symm).elim
      · exact (second_not_end s p1 h1 (e,b) h.symm).elim
    · cases b
      · exact (first_not_end s p0 h0 (e',b') h).elim
      · exact (second_not_end s p1 h1 (e',b') h).elim
    · cases u; cases u'; cases b <;> cases b'
      · rfl
      · have hh := s.boundary.injective h
        have : (0 : Fin (n+2))≠1 := by intro h; have := congrArg Fin.val h; simp at this
        exact (this hh).elim
      · have hh := s.boundary.injective h
        have : (1 : Fin (n+2))≠0 := by intro h; have := congrArg Fin.val h; simp at this
        exact (this hh).elim
      · rfl

theorem paired_iff (p : Ports V F s.arity) :
    (∃e,ends s p0 p1 h0 h1 e=p) ↔
      (∃e,s.ends e=p) ∨ s.boundary 0=p ∨ s.boundary 1=p := by
  constructor
  · rintro ⟨⟨(e|u),b⟩,h⟩
    · exact Or.inl ⟨(e,b),h⟩
    · cases b
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rintro (⟨e,h⟩ | h | h)
    · exact ⟨(.inl e.1,e.2),h⟩
    · exact ⟨(.inr (),false),h⟩
    · exact ⟨(.inr (),true),h⟩

theorem ordinary_rule (p : Σ v,Fin (s.arity v)) :
    (∃j,boundary s j=.inl p) ↔ ¬∃e,ends s p0 p1 h0 h1 e=.inl p := by
  rw [paired_iff]
  constructor
  · rintro ⟨j,hj⟩ (he | he | he)
    · exact (s.ordinary_boundary_iff_unpaired p).mp ⟨j.succ.succ,hj⟩ he
    · have hh := s.boundary.injective (hj.trans he.symm)
      have := congrArg Fin.val hh
      simp at this
    · have hh := s.boundary.injective (hj.trans he.symm)
      have := congrArg Fin.val hh
      simp at this
  · intro hn
    obtain ⟨j,hj⟩ := (s.ordinary_boundary_iff_unpaired p).mpr (fun h => hn (Or.inl h))
    cases j using Fin.cases with
    | zero => exact (hn (Or.inr (Or.inl hj))).elim
    | succ j =>
      cases j using Fin.cases with
      | zero => exact (hn (Or.inr (Or.inr hj))).elim
      | succ k => exact ⟨k,hj⟩

include h0 h1 in
theorem free_boundary_exists (f : F) : ∃j,boundary s j=.inr f := by
  have hf := s.free_boundary f
  generalize hj : s.freeBoundary f=j at hf
  cases j using Fin.cases with
  | zero =>
    rw [h0] at hf
    cases hf
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      have hh : s.boundary 1=.inr f := by simpa using hf
      rw [h1] at hh
      cases hh
    | succ k => exact ⟨k,hf⟩

def shape : FiniteShape V F (E ⊕ Unit) n where
  arity := s.arity
  boundary := boundary s
  ends := ends s p0 p1 h0 h1
  ordinary_boundary_iff_unpaired := ordinary_rule s p0 p1 h0 h1
  freeBoundary := fun f => Classical.choose (free_boundary_exists s p0 p1 h0 h1 f)
  free_boundary := fun f => Classical.choose_spec (free_boundary_exists s p0 p1 h0 h1 f)
  freeEdge := fun f => (.inl (s.freeEdge f).1,(s.freeEdge f).2)
  free_paired := fun f => s.free_paired f

end Holant.OpenNetworkComposition.ProjectiveContraction.Ordinary
