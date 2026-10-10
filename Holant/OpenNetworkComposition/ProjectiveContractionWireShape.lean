import Holant.OpenNetworkComposition.FreeFree

/-! Remove one isolated native wire whose two endpoints are free boundaries.
No vertex is deleted or added. A supplied boundary embedding records exactly
the surviving old coordinates, so subsequent contractions retain their order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Wire
open FiniteShape
variable {V F E : Type*} {m n : ℕ}

abbrev CutTwo (f g : F) := {h : F // h≠f ∧ h≠g}

def embed (s : FiniteShape V F E m) (f g : F) : Ports V (CutTwo f g) s.arity ↪ Ports V F s.arity where
  toFun := Sum.map id Subtype.val
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all
    exact Subtype.ext h

@[simp] theorem embed_inl (s : FiniteShape V F E m) (f g : F) (p : Σv,Fin (s.arity v)) :
    embed s f g (.inl p)=.inl p := rfl
@[simp] theorem embed_inr (s : FiniteShape V F E m) (f g : F) (h : CutTwo f g) :
    embed s f g (.inr h)=.inr h.val := rfl

theorem embed_ne_first (s : FiniteShape V F E m) (f g : F) (p : Ports V (CutTwo f g) s.arity) :
    embed s f g p≠.inr f := by
  cases p with
  | inl p => simp
  | inr h => simpa using h.property.1

theorem embed_ne_second (s : FiniteShape V F E m) (f g : F) (p : Ports V (CutTwo f g) s.arity) :
    embed s f g p≠.inr g := by
  cases p with
  | inl p => simp
  | inr h => simpa using h.property.2

def port (s : FiniteShape V F E m) (f g : F) (p : Ports V F s.arity)
    (hf : p≠.inr f) (hg : p≠.inr g) : Ports V (CutTwo f g) s.arity :=
  match p with
  | .inl p => .inl p
  | .inr h => .inr ⟨h,fun hh => hf (congrArg Sum.inr hh),fun hh => hg (congrArg Sum.inr hh)⟩

@[simp] theorem embed_port (s : FiniteShape V F E m) (f g : F) (p : Ports V F s.arity)
    (hf : p≠.inr f) (hg : p≠.inr g) : embed s f g (port s f g p hf hg)=p := by
  cases p <;> rfl

variable (s : FiniteShape V F E m) (f g : F)
    (hop : s.ends ((s.freeEdge f).1,!(s.freeEdge f).2)=.inr g)

include hop in
theorem removed_end (b : Bool) : s.ends ((s.freeEdge f).1,b)=
    if b=(s.freeEdge f).2 then .inr f else .inr g := by
  by_cases hb : b=(s.freeEdge f).2
  · rw [ite_eq_left hb,hb]
    exact s.free_paired f
  · rw [ite_eq_right hb]
    have hn : b=!(s.freeEdge f).2 := by cases b <;> cases h : (s.freeEdge f).2 <;> simp_all
    rw [hn]
    exact hop

include hop in
theorem retained_ne_second (e : s.CutEdge f) (b : Bool) : s.ends (e.val,b)≠.inr g := by
  intro h
  exact e.property (congrArg Prod.fst (s.ends.injective (h.trans hop.symm)))

def ends : (s.CutEdge f × Bool) ↪ Ports V (CutTwo f g) s.arity where
  toFun e := port s f g (s.ends (e.1.val,e.2))
    (s.retained_end_ne f e.1 e.2) (retained_ne_second s f g hop e.1 e.2)
  inj' := by
    intro a b h
    have hh := congrArg (embed s f g) h
    simp only [embed_port] at hh
    have he := s.ends.injective hh
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (congrArg (fun q : E × Bool => q.2) he)

@[simp] theorem embed_ends (e : s.CutEdge f × Bool) :
    embed s f g (ends s f g hop e)=s.ends (e.1.val,e.2) := by
  exact embed_port s f g _ _ _

theorem paired_iff (p : Ports V (CutTwo f g) s.arity) :
    (∃e,ends s f g hop e=p) ↔ ∃e,s.ends e=embed s f g p := by
  constructor
  · rintro ⟨e,he⟩
    exact ⟨(e.1.val,e.2),by rw [←embed_ends s f g hop e,he]⟩
  · rintro ⟨⟨e,b⟩,he⟩
    by_cases hdel : e=(s.freeEdge f).1
    · subst e
      rw [removed_end s f g hop] at he
      split_ifs at he with hb
      · exact (embed_ne_first s f g p he.symm).elim
      · exact (embed_ne_second s f g p he.symm).elim
    · refine ⟨(⟨e,hdel⟩,b),?_⟩
      apply (embed s f g).injective
      simpa using he

variable (i j : Fin m) (hi : s.boundary i=.inr f) (hj : s.boundary j=.inr g)
    (β : Fin n ↪ Fin m) (hβ : ∀k,(∃l,β l=k) ↔ k≠i ∧ k≠j)

def boundary : Fin n ↪ Ports V (CutTwo f g) s.arity where
  toFun k := port s f g (s.boundary (β k))
    (s.boundary_ne_selected f i hi (β k) ((hβ (β k)).mp ⟨k,rfl⟩).1)
    (s.boundary_ne_selected g j hj (β k) ((hβ (β k)).mp ⟨k,rfl⟩).2)
  inj' := by
    intro a b h
    have hh := congrArg (embed s f g) h
    simp only [embed_port] at hh
    exact β.injective (s.boundary.injective hh)

@[simp] theorem embed_boundary (k : Fin n) :
    embed s f g (boundary s f g i j hi hj β hβ k)=s.boundary (β k) := by
  exact embed_port s f g _ _ _

theorem ordinary_rule (p : Σv,Fin (s.arity v)) :
    (∃k,boundary s f g i j hi hj β hβ k=.inl p) ↔ ¬∃e,ends s f g hop e=.inl p := by
  rw [paired_iff,embed_inl,←s.ordinary_boundary_iff_unpaired p]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨β k,by simpa using congrArg (embed s f g) hk⟩
  · rintro ⟨k,hk⟩
    have hki : k≠i := by intro h; subst k; rw [hi] at hk; cases hk
    have hkj : k≠j := by intro h; subst k; rw [hj] at hk; cases hk
    obtain ⟨l,hl⟩ := (hβ k).mpr ⟨hki,hkj⟩
    refine ⟨l,?_⟩
    apply (embed s f g).injective
    simpa [hl] using hk

theorem free_boundary_exists (h : CutTwo f g) :
    ∃k,boundary s f g i j hi hj β hβ k=.inr h := by
  have hki : s.freeBoundary h.val≠i := by
    intro hk
    have hh := s.free_boundary h.val
    rw [hk,hi] at hh
    exact h.property.1 (Sum.inr.inj hh).symm
  have hkj : s.freeBoundary h.val≠j := by
    intro hk
    have hh := s.free_boundary h.val
    rw [hk,hj] at hh
    exact h.property.2 (Sum.inr.inj hh).symm
  obtain ⟨k,hk⟩ := (hβ (s.freeBoundary h.val)).mpr ⟨hki,hkj⟩
  refine ⟨k,?_⟩
  apply (embed s f g).injective
  simpa [hk] using s.free_boundary h.val

include hop in
theorem free_paired_exists (h : CutTwo f g) : ∃e,ends s f g hop e=.inr h := by
  exact (paired_iff s f g hop (.inr h)).mpr ⟨s.freeEdge h.val,s.free_paired h.val⟩

def shape : FiniteShape V (CutTwo f g) (s.CutEdge f) n where
  arity := s.arity
  boundary := boundary s f g i j hi hj β hβ
  ends := ends s f g hop
  ordinary_boundary_iff_unpaired := ordinary_rule s f g hop i j hi hj β hβ
  freeBoundary := fun h => Classical.choose (free_boundary_exists s f g i j hi hj β hβ h)
  free_boundary := fun h => Classical.choose_spec (free_boundary_exists s f g i j hi hj β hβ h)
  freeEdge := fun h => Classical.choose (free_paired_exists s f g hop h)
  free_paired := fun h => Classical.choose_spec (free_paired_exists s f g hop h)

end Holant.OpenNetworkComposition.ProjectiveContraction.Wire
