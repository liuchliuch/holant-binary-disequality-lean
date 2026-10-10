import Holant.OpenNetworkComposition.FreeFree
import Holant.OpenNetworkComposition.OrdinaryPorts
import Mathlib.Tactic.FinCases

/-! Mixed disjoint one-port splice: the left selected endpoint is ordinary,
the right selected endpoint is free. Only that free stub and its edge are
removed; a native edge joins the left port to the surviving right opposite end. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.OrdinaryFree
open FiniteShape
variable {VL FL EL VR FR ER : Type*} {n : ℕ}
variable (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2) (f : FR) (i : Fin n)
abbrev JoinPorts := Ports VL FL L.arity ⊕ R.CutPorts f
abbrev JoinEdges := (EL ⊕ R.CutEdge f) ⊕ Unit

def endFn : JoinEdges (EL := EL) R f × Bool → JoinPorts L R f
  | (.inl (.inl e),b) => .inl (L.ends (e,b))
  | (.inl (.inr e),b) => .inr (R.cutEnds f (e,b))
  | (.inr _,false) => .inl (L.boundary i)
  | (.inr _,true) => .inr (R.cutOpposite f)

variable (p : Σ v,Fin (L.arity v)) (hL : L.boundary i=.inl p) (hR : R.boundary 1=.inr f)

def ends : JoinEdges (EL := EL) R f × Bool ↪ JoinPorts L R f where
  toFun := endFn L R f i
  inj' := by
    rintro ⟨((e|e)|u),b⟩ ⟨((e'|e')|u'),b'⟩ h
    · have hh := L.ends.injective (Sum.inl.inj h)
      cases hh; rfl
    · cases h
    · cases b'
      · exact (Ordinary.selected_not_end_left L i p hL (e,b) (Sum.inl.inj h).symm).elim
      · cases h
    · cases h
    · have hh := (R.cutEnds f).injective (Sum.inr.inj h)
      cases hh; rfl
    · cases b'
      · cases h
      · exact (R.cutEnds_ne_opposite f (e,b) (Sum.inr.inj h)).elim
    · cases b
      · exact (Ordinary.selected_not_end_left L i p hL (e',b') (Sum.inl.inj h)).elim
      · cases h
    · cases b
      · cases h
      · exact (R.cutEnds_ne_opposite f (e',b') (Sum.inr.inj h).symm).elim
    · cases u; cases u'; cases b <;> cases b' <;> first | rfl | cases h

def boundaryFn (j : Fin n) : JoinPorts L R f :=
  if j=i then .inr (R.cutBoundary f 1 hR ⟨0,by decide⟩) else .inl (L.boundary j)

def boundary : Fin n ↪ JoinPorts L R f where
  toFun := boundaryFn L R f i hR
  inj' := by
    intro a b h
    by_cases ha : a=i <;> by_cases hb : b=i
    · exact ha.trans hb.symm
    · simp [boundaryFn,ha,hb] at h
    · simp [boundaryFn,ha,hb] at h
    · simp only [boundaryFn,ite_eq_right ha,ite_eq_right hb,Sum.inl.injEq] at h
      exact L.boundary.injective h

@[simp] theorem boundary_at : boundary L R f i hR i=.inr (R.cutBoundary f 1 hR ⟨0,by decide⟩) := by
  simp [boundary,boundaryFn]
theorem boundary_away (j : Fin n) (hj : j≠i) : boundary L R f i hR j=.inl (L.boundary j) := by
  simp [boundary,boundaryFn,hj]

theorem paired_left_iff (a : Ports VL FL L.arity) :
    (∃e,ends L R f i p hL e=.inl a) ↔ (∃e,L.ends e=a) ∨ L.boundary i=a := by
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

theorem paired_right_iff (a : R.CutPorts f) :
    (∃e,ends L R f i p hL e=.inr a) ↔ ∃e,R.ends e=R.cutEmbed f a := by
  rw [R.cut_paired_iff]
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
    (∃j,boundary L R f i hR j=.inl (.inl a)) ↔
      ¬∃e,ends L R f i p hL e=.inl (.inl a) := by
  rw [paired_left_iff]
  constructor
  · rintro ⟨j,hj⟩ (he|hi)
    · by_cases hji : j=i
      · subst j; simp at hj
      · rw [boundary_away L R f i hR j hji] at hj
        exact (L.ordinary_boundary_iff_unpaired a).mp ⟨j,Sum.inl.inj hj⟩ he
    · by_cases hji : j=i
      · subst j; simp at hj
      · rw [boundary_away L R f i hR j hji] at hj
        exact hji (L.boundary.injective ((Sum.inl.inj hj).trans hi.symm))
  · intro h
    obtain ⟨j,hj⟩ := (L.ordinary_boundary_iff_unpaired a).mpr (fun he => h (Or.inl he))
    have hji : j≠i := by intro hi; subst j; exact h (Or.inr hj)
    exact ⟨j,by rw [boundary_away L R f i hR j hji,hj]⟩

theorem ordinary_right (a : Σ v,Fin (R.arity v)) :
    (∃j,boundary L R f i hR j=.inr (.inl a)) ↔ ∃j,R.boundary j=.inl a := by
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j
      rw [boundary_at] at hj
      exact ⟨0,by simpa using congrArg (R.cutEmbed f) (Sum.inr.inj hj)⟩
    · rw [boundary_away L R f i hR j hji] at hj
      cases hj
  · rintro ⟨j,hj⟩
    have hj0 : j=0 := by
      fin_cases j
      · rfl
      · have hh : R.boundary 1=.inl a := hj
        rw [hR] at hh; cases hh
    subst j
    refine ⟨i,?_⟩
    rw [boundary_at]
    apply congrArg Sum.inr
    apply (R.cutEmbed f).injective
    simpa using hj

include hL in
theorem free_boundary_exists (g : FL ⊕ CutFree f) :
    ∃j,boundary L R f i hR j=(portSum L.arity R.arity) (.inr g) := by
  cases g with
  | inl g =>
    have hj : L.freeBoundary g≠i := by
      intro hi
      have hh := L.free_boundary g
      rw [hi,hL] at hh; cases hh
    exact ⟨L.freeBoundary g,by rw [boundary_away L R f i hR _ hj,L.free_boundary]; rfl⟩
  | inr g =>
    have hj1 : R.freeBoundary g.val≠1 := by
      intro hi
      have hh := R.free_boundary g.val
      rw [hi,hR] at hh
      exact g.property (Sum.inr.inj hh).symm
    have hj0 : R.freeBoundary g.val=0 := by
      have h : ∀j:Fin 2,j≠1 → j=0 := by intro j h; fin_cases j <;> simp_all
      exact h _ hj1
    refine ⟨i,?_⟩
    rw [boundary_at]
    apply congrArg Sum.inr
    apply (R.cutEmbed f).injective
    have hh := R.free_boundary g.val
    rw [hj0] at hh
    simpa using hh

theorem free_pair_exists (g : FL ⊕ CutFree f) :
    ∃e,ends L R f i p hL e=(portSum L.arity R.arity) (.inr g) := by
  cases g with
  | inl g => exact (paired_left_iff L R f i p hL (.inr g)).mpr (Or.inl ⟨L.freeEdge g,L.free_paired g⟩)
  | inr g => exact (paired_right_iff L R f i p hL (.inr g)).mpr ⟨R.freeEdge g.val,R.free_paired g.val⟩

abbrev shape : FiniteShape (VL ⊕ VR) (FL ⊕ CutFree f) (JoinEdges (EL := EL) R f) n where
  arity := SumArity L.arity R.arity
  boundary := (boundary L R f i hR).trans (portSum L.arity R.arity).symm.toEmbedding
  ends := (ends L R f i p hL).trans (portSum L.arity R.arity).symm.toEmbedding
  ordinary_boundary_iff_unpaired := by
    rintro ⟨(v|v),k⟩
    · change (∃j,(portSum L.arity R.arity).symm (boundary L R f i hR j)=
          (portSum L.arity R.arity).symm (.inl (.inl ⟨v,k⟩))) ↔
        ¬∃e,(portSum L.arity R.arity).symm (ends L R f i p hL e)=
          (portSum L.arity R.arity).symm (.inl (.inl ⟨v,k⟩))
      simp only [Equiv.apply_eq_iff_eq]
      exact ordinary_left L R f i p hL hR ⟨v,k⟩
    · change (∃j,(portSum L.arity R.arity).symm (boundary L R f i hR j)=
          (portSum L.arity R.arity).symm (.inr (.inl ⟨v,k⟩))) ↔
        ¬∃e,(portSum L.arity R.arity).symm (ends L R f i p hL e)=
          (portSum L.arity R.arity).symm (.inr (.inl ⟨v,k⟩))
      simp only [Equiv.apply_eq_iff_eq]
      rw [ordinary_right,paired_right_iff]
      exact R.ordinary_boundary_iff_unpaired ⟨v,k⟩
  freeBoundary := fun g => Classical.choose (free_boundary_exists L R f i p hL hR g)
  free_boundary := by
    intro g
    change (portSum L.arity R.arity).symm _=_
    rw [Classical.choose_spec (free_boundary_exists L R f i p hL hR g)]
    exact (portSum L.arity R.arity).symm_apply_apply _
  freeEdge := fun g => Classical.choose (free_pair_exists L R f i p hL g)
  free_paired := by
    intro g
    change (portSum L.arity R.arity).symm _=_
    rw [Classical.choose_spec (free_pair_exists L R f i p hL g)]
    exact (portSum L.arity R.arity).symm_apply_apply _

end Holant.OpenNetworkComposition.OrdinaryFree
