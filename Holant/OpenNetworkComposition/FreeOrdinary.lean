import Holant.OpenNetworkComposition.FreeFree
import Holant.OpenNetworkComposition.OrdinaryPorts
import Mathlib.Tactic.FinCases

/-! Mixed disjoint splice with selected left free stub and selected right
ordinary port. The removed left edge is replaced by one native edge from its
surviving opposite endpoint to the selected right ordinary occurrence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.FreeOrdinary
open FiniteShape
variable {VL FL EL VR FR ER : Type*} {n : ℕ}
variable (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2) (f : FL) (i : Fin n)
abbrev JoinPorts := L.CutPorts f ⊕ Ports VR FR R.arity
abbrev JoinEdges := (L.CutEdge f ⊕ ER) ⊕ Unit

def endFn : JoinEdges (ER := ER) L f × Bool → JoinPorts L R f
  | (.inl (.inl e),b) => .inl (L.cutEnds f (e,b))
  | (.inl (.inr e),b) => .inr (R.ends (e,b))
  | (.inr _,false) => .inl (L.cutOpposite f)
  | (.inr _,true) => .inr (R.boundary 1)

variable (p : Σ v,Fin (R.arity v)) (hL : L.boundary i=.inr f) (hR : R.boundary 1=.inl p)

def ends : JoinEdges (ER := ER) L f × Bool ↪ JoinPorts L R f where
  toFun := endFn L R f
  inj' := by
    rintro ⟨((e|e)|u),b⟩ ⟨((e'|e')|u'),b'⟩ h
    · have hh := (L.cutEnds f).injective (Sum.inl.inj h)
      cases hh; rfl
    · cases h
    · cases b'
      · exact (L.cutEnds_ne_opposite f (e,b) (Sum.inl.inj h)).elim
      · cases h
    · cases h
    · have hh := R.ends.injective (Sum.inr.inj h)
      cases hh; rfl
    · cases b'
      · cases h
      · exact (Ordinary.selected_not_end_right R p hR (e,b) (Sum.inr.inj h).symm).elim
    · cases b
      · exact (L.cutEnds_ne_opposite f (e',b') (Sum.inl.inj h).symm).elim
      · cases h
    · cases b
      · cases h
      · exact (Ordinary.selected_not_end_right R p hR (e',b') (Sum.inr.inj h)).elim
    · cases u; cases u'; cases b <;> cases b' <;> first | rfl | cases h

def boundaryFn (j : Fin n) : JoinPorts L R f :=
  if hj : j=i then .inr (R.boundary 0) else .inl (L.cutBoundary f i hL ⟨j,hj⟩)

def boundary : Fin n ↪ JoinPorts L R f where
  toFun := boundaryFn L R f i hL
  inj' := by
    intro a b h
    by_cases ha : a=i <;> by_cases hb : b=i
    · exact ha.trans hb.symm
    · simp [boundaryFn,ha,hb] at h
    · simp [boundaryFn,ha,hb] at h
    · simp only [boundaryFn,dite_eq_right ha,dite_eq_right hb,Sum.inl.injEq] at h
      exact congrArg Subtype.val ((L.cutBoundary f i hL).injective h)

@[simp] theorem boundary_at : boundary L R f i hL i=.inr (R.boundary 0) := by simp [boundary,boundaryFn]
theorem boundary_away (j : Fin n) (hj : j≠i) :
    boundary L R f i hL j=.inl (L.cutBoundary f i hL ⟨j,hj⟩) := by simp [boundary,boundaryFn,hj]

theorem paired_left_iff (a : L.CutPorts f) :
    (∃e,ends L R f p hR e=.inl a) ↔ ∃e,L.ends e=L.cutEmbed f a := by
  rw [L.cut_paired_iff]
  constructor
  · rintro ⟨⟨((e|e)|u),b⟩,h⟩
    · exact Or.inl ⟨(e,b),Sum.inl.inj h⟩
    · cases h
    · cases b
      · exact Or.inr (Sum.inl.inj h)
      · cases h
  · rintro (⟨e,h⟩|h)
    · exact ⟨(.inl (.inl e.1),e.2),congrArg Sum.inl h⟩
    · exact ⟨(.inr (),false),congrArg Sum.inl h⟩

theorem paired_right_iff (a : Ports VR FR R.arity) :
    (∃e,ends L R f p hR e=.inr a) ↔ (∃e,R.ends e=a) ∨ R.boundary 1=a := by
  constructor
  · rintro ⟨⟨((e|e)|u),b⟩,h⟩
    · cases h
    · exact Or.inl ⟨(e,b),Sum.inr.inj h⟩
    · cases b
      · cases h
      · exact Or.inr (Sum.inr.inj h)
  · rintro (⟨e,h⟩|h)
    · exact ⟨(.inl (.inr e.1),e.2),congrArg Sum.inr h⟩
    · exact ⟨(.inr (),true),congrArg Sum.inr h⟩

theorem ordinary_left (a : Σ v,Fin (L.arity v)) :
    (∃j,boundary L R f i hL j=.inl (.inl a)) ↔ ∃j,L.boundary j=.inl a := by
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j; simp at hj
    · rw [boundary_away L R f i hL j hji] at hj
      exact ⟨j,by simpa using congrArg (L.cutEmbed f) (Sum.inl.inj hj)⟩
  · rintro ⟨j,hj⟩
    have hji : j≠i := by intro hi; subst j; rw [hL] at hj; cases hj
    refine ⟨j,?_⟩
    rw [boundary_away L R f i hL j hji]
    apply congrArg Sum.inl
    apply (L.cutEmbed f).injective
    simpa using hj

theorem ordinary_right (a : Σ v,Fin (R.arity v)) :
    (∃j,boundary L R f i hL j=.inr (.inl a)) ↔
      ¬∃e,ends L R f p hR e=.inr (.inl a) := by
  rw [paired_right_iff]
  constructor
  · rintro ⟨j,hj⟩
    have hh : R.boundary 0=.inl a := by
      by_cases hji : j=i
      · subst j; rw [boundary_at] at hj; exact Sum.inr.inj hj
      · rw [boundary_away L R f i hL j hji] at hj; cases hj
    rintro (he|hi)
    · exact (R.ordinary_boundary_iff_unpaired a).mp ⟨0,hh⟩ he
    · exact (by decide : (0 : Fin 2)≠1) (R.boundary.injective (hh.trans hi.symm))
  · intro h
    obtain ⟨j,hj⟩ := (R.ordinary_boundary_iff_unpaired a).mpr (fun he => h (Or.inl he))
    have hj0 : j=0 := by
      fin_cases j
      · rfl
      · exact (h (Or.inr hj)).elim
    subst j
    exact ⟨i,by rw [boundary_at,hj]⟩

include hR in
theorem free_boundary_exists (g : CutFree f ⊕ FR) :
    ∃j,boundary L R f i hL j=(portSum L.arity R.arity) (.inr g) := by
  cases g with
  | inl g =>
    have hj : L.freeBoundary g.val≠i := by
      intro hi
      have hh := L.free_boundary g.val
      rw [hi,hL] at hh
      exact g.property (Sum.inr.inj hh).symm
    refine ⟨L.freeBoundary g.val,?_⟩
    rw [boundary_away L R f i hL _ hj]
    apply congrArg Sum.inl
    apply (L.cutEmbed f).injective
    simpa using L.free_boundary g.val
  | inr g =>
    have hj1 : R.freeBoundary g≠1 := by
      intro hi
      have hh := R.free_boundary g
      rw [hi,hR] at hh; cases hh
    have hj0 : R.freeBoundary g=0 := by
      have h : ∀j:Fin 2,j≠1 → j=0 := by intro j h; fin_cases j <;> simp_all
      exact h _ hj1
    refine ⟨i,?_⟩
    rw [boundary_at]
    have hh := R.free_boundary g
    rw [hj0] at hh
    exact congrArg Sum.inr hh

theorem free_pair_exists (g : CutFree f ⊕ FR) :
    ∃e,ends L R f p hR e=(portSum L.arity R.arity) (.inr g) := by
  cases g with
  | inl g => exact (paired_left_iff L R f p hR (.inr g)).mpr ⟨L.freeEdge g.val,L.free_paired g.val⟩
  | inr g => exact (paired_right_iff L R f p hR (.inr g)).mpr (Or.inl ⟨R.freeEdge g,R.free_paired g⟩)

abbrev shape : FiniteShape (VL ⊕ VR) (CutFree f ⊕ FR) (JoinEdges (ER := ER) L f) n where
  arity := SumArity L.arity R.arity
  boundary := (boundary L R f i hL).trans (portSum L.arity R.arity).symm.toEmbedding
  ends := (ends L R f p hR).trans (portSum L.arity R.arity).symm.toEmbedding
  ordinary_boundary_iff_unpaired := by
    rintro ⟨(v|v),k⟩
    · change (∃j,(portSum L.arity R.arity).symm (boundary L R f i hL j)=
          (portSum L.arity R.arity).symm (.inl (.inl ⟨v,k⟩))) ↔
        ¬∃e,(portSum L.arity R.arity).symm (ends L R f p hR e)=
          (portSum L.arity R.arity).symm (.inl (.inl ⟨v,k⟩))
      simp only [Equiv.apply_eq_iff_eq]
      rw [ordinary_left,paired_left_iff]
      exact L.ordinary_boundary_iff_unpaired ⟨v,k⟩
    · change (∃j,(portSum L.arity R.arity).symm (boundary L R f i hL j)=
          (portSum L.arity R.arity).symm (.inr (.inl ⟨v,k⟩))) ↔
        ¬∃e,(portSum L.arity R.arity).symm (ends L R f p hR e)=
          (portSum L.arity R.arity).symm (.inr (.inl ⟨v,k⟩))
      simp only [Equiv.apply_eq_iff_eq]
      exact ordinary_right L R f i p hL hR ⟨v,k⟩
  freeBoundary := fun g => Classical.choose (free_boundary_exists L R f i p hL hR g)
  free_boundary := by
    intro g
    change (portSum L.arity R.arity).symm _=_
    rw [Classical.choose_spec (free_boundary_exists L R f i p hL hR g)]
    exact (portSum L.arity R.arity).symm_apply_apply _
  freeEdge := fun g => Classical.choose (free_pair_exists L R f p hR g)
  free_paired := by
    intro g
    change (portSum L.arity R.arity).symm _=_
    rw [Classical.choose_spec (free_pair_exists L R f p hR g)]
    exact (portSum L.arity R.arity).symm_apply_apply _

end Holant.OpenNetworkComposition.FreeOrdinary
