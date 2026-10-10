import Holant.OpenNetworkComposition.FreeFree
import Holant.OpenNetworkComposition.PortSum
import Mathlib.Tactic.FinCases

/-! Disjoint free/free splice incidence. Exactly the two selected free stubs and
their old edges are removed; the two surviving opposite endpoints are joined. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.FreeFree
open FiniteShape
variable {VL FL EL VR FR ER : Type*} {n : ℕ}

abbrev SplicePorts (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2)
    (fL : FL) (fR : FR) := L.CutPorts fL ⊕ R.CutPorts fR
abbrev SpliceEdges (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2)
    (fL : FL) (fR : FR) := (L.CutEdge fL ⊕ R.CutEdge fR) ⊕ Unit

def endFn (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2)
    (fL : FL) (fR : FR) : SpliceEdges L R fL fR × Bool → SplicePorts L R fL fR
  | (.inl (.inl e),b) => .inl (L.cutEnds fL (e,b))
  | (.inl (.inr e),b) => .inr (R.cutEnds fR (e,b))
  | (.inr _,false) => .inl (L.cutOpposite fL)
  | (.inr _,true) => .inr (R.cutOpposite fR)

def ends (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2)
    (fL : FL) (fR : FR) : (SpliceEdges L R fL fR × Bool) ↪ SplicePorts L R fL fR where
  toFun := endFn L R fL fR
  inj' := by
    rintro ⟨(e|u),b⟩ ⟨(e'|u'),b'⟩ h
    · rcases e with e|e <;> rcases e' with e'|e'
      · have hh := (L.cutEnds fL).injective (Sum.inl.inj h)
        simpa only [Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq] using hh
      · cases h
      · cases h
      · have hh := (R.cutEnds fR).injective (Sum.inr.inj h)
        simpa only [Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq] using hh
    · rcases e with e|e <;> cases b'
      · exact False.elim (L.cutEnds_ne_opposite fL (e,b) (Sum.inl.inj h))
      · cases h
      · cases h
      · exact False.elim (R.cutEnds_ne_opposite fR (e,b) (Sum.inr.inj h))
    · rcases e' with e'|e' <;> cases b
      · exact False.elim (L.cutEnds_ne_opposite fL (e',b') (Sum.inl.inj h).symm)
      · cases h
      · cases h
      · exact False.elim (R.cutEnds_ne_opposite fR (e',b') (Sum.inr.inj h).symm)
    · cases u; cases u'; cases b <;> cases b' <;> first | rfl | cases h

/-- Pairing of every surviving left endpoint is exactly its old pairing. -/
theorem paired_left_iff (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2)
    (fL : FL) (fR : FR) (p : L.CutPorts fL) :
    (∃ eb,ends L R fL fR eb=.inl p) ↔ (∃ eb,L.ends eb=L.cutEmbed fL p) := by
  rw [L.cut_paired_iff]
  constructor
  · rintro ⟨⟨((e|e)|u),b⟩,h⟩
    · exact Or.inl ⟨(e,b),Sum.inl.inj h⟩
    · cases h
    · cases b
      · exact Or.inr (Sum.inl.inj h)
      · cases h
  · rintro (⟨eb,h⟩|h)
    · exact ⟨(.inl (.inl eb.1),eb.2),congrArg Sum.inl h⟩
    · exact ⟨(.inr (),false),congrArg Sum.inl h⟩

theorem paired_right_iff (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2)
    (fL : FL) (fR : FR) (p : R.CutPorts fR) :
    (∃ eb,ends L R fL fR eb=.inr p) ↔ (∃ eb,R.ends eb=R.cutEmbed fR p) := by
  rw [R.cut_paired_iff]
  constructor
  · rintro ⟨⟨((e|e)|u),b⟩,h⟩
    · cases h
    · exact Or.inl ⟨(e,b),Sum.inr.inj h⟩
    · cases b
      · cases h
      · exact Or.inr (Sum.inr.inj h)
  · rintro (⟨eb,h⟩|h)
    · exact ⟨(.inl (.inr eb.1),eb.2),congrArg Sum.inr h⟩
    · exact ⟨(.inr (),true),congrArg Sum.inr h⟩

variable (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2)
    (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.boundary i=.inr fL) (hR : R.boundary 1=.inr fR)

def boundaryFn (j : Fin n) : SplicePorts L R fL fR :=
  if hj : j=i then .inr (R.cutBoundary fR 1 hR ⟨0,by decide⟩)
  else .inl (L.cutBoundary fL i hL ⟨j,hj⟩)

def boundary : Fin n ↪ SplicePorts L R fL fR where
  toFun := boundaryFn L R fL fR i hL hR
  inj' := by
    intro a b h
    by_cases ha : a=i <;> by_cases hb : b=i
    · exact ha.trans hb.symm
    · simp [boundaryFn,ha,hb] at h
    · simp [boundaryFn,ha,hb] at h
    · simp only [boundaryFn,dite_eq_right ha,dite_eq_right hb,Sum.inl.injEq] at h
      exact congrArg Subtype.val ((L.cutBoundary fL i hL).injective h)

@[simp] theorem boundary_at : boundary L R fL fR i hL hR i =
    .inr (R.cutBoundary fR 1 hR ⟨0,by decide⟩) := by simp [boundary,boundaryFn]

theorem boundary_away (j : Fin n) (hj : j≠i) : boundary L R fL fR i hL hR j =
    .inl (L.cutBoundary fL i hL ⟨j,hj⟩) := by simp [boundary,boundaryFn,hj]

/-- Ordinary boundary membership on the left is unchanged. -/
theorem ordinary_boundary_left (p : Σ v,Fin (L.arity v)) :
    (∃ j,boundary L R fL fR i hL hR j=.inl (.inl p)) ↔
    (∃ j,L.boundary j=.inl p) := by
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j; simp at hj
    · rw [boundary_away L R fL fR i hL hR j hji] at hj
      refine ⟨j,?_⟩
      have h := congrArg (L.cutEmbed fL) (Sum.inl.inj hj)
      simpa using h
  · rintro ⟨j,hj⟩
    have hji : j≠i := by intro h; subst j; rw [hL] at hj; cases hj
    refine ⟨j,?_⟩
    rw [boundary_away L R fL fR i hL hR j hji]
    apply congrArg Sum.inl
    apply (L.cutEmbed fL).injective
    simpa using hj

/-- Right port 1 was free, so every surviving right ordinary boundary is port 0. -/
theorem ordinary_boundary_right (p : Σ v,Fin (R.arity v)) :
    (∃ j,boundary L R fL fR i hL hR j=.inr (.inl p)) ↔
    (∃ j,R.boundary j=.inl p) := by
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j
      rw [boundary_at] at hj
      refine ⟨0,?_⟩
      have h := congrArg (R.cutEmbed fR) (Sum.inr.inj hj)
      simpa using h
    · rw [boundary_away L R fL fR i hL hR j hji] at hj
      cases hj
  · rintro ⟨j,hj⟩
    have hj1 : j≠1 := by intro h; subst j; rw [hR] at hj; cases hj
    have hj0 : j=0 := by fin_cases j <;> simp_all
    subst j
    refine ⟨i,?_⟩
    rw [boundary_at]
    apply congrArg Sum.inr
    apply (R.cutEmbed fR).injective
    simpa using hj

theorem free_boundary_exists (f : CutFree fL ⊕ CutFree fR) :
    ∃ j,boundary L R fL fR i hL hR j =
      (portSum L.arity R.arity) (.inr f) := by
  cases f with
  | inl g =>
    have hj : L.freeBoundary g.val ≠ i := by
      intro h
      have hh := L.free_boundary g.val
      rw [h,hL] at hh
      exact g.property (Sum.inr.inj hh).symm
    refine ⟨L.freeBoundary g.val,?_⟩
    rw [boundary_away L R fL fR i hL hR _ hj]
    apply congrArg Sum.inl
    apply (L.cutEmbed fL).injective
    simpa using L.free_boundary g.val
  | inr g =>
    have hj : R.freeBoundary g.val ≠ 1 := by
      intro h
      have hh := R.free_boundary g.val
      rw [h,hR] at hh
      exact g.property (Sum.inr.inj hh).symm
    have hj0 : R.freeBoundary g.val = 0 := by
      have hh : ∀ j : Fin 2,j≠1 → j=0 := by
        intro j h; fin_cases j <;> simp_all
      exact hh _ hj
    refine ⟨i,?_⟩
    rw [boundary_at]
    apply congrArg Sum.inr
    apply (R.cutEmbed fR).injective
    have hh := R.free_boundary g.val
    rw [hj0] at hh
    simpa using hh

theorem free_pair_exists (f : CutFree fL ⊕ CutFree fR) :
    ∃ eb,ends L R fL fR eb = (portSum L.arity R.arity) (.inr f) := by
  cases f with
  | inl g =>
    apply (paired_left_iff L R fL fR (.inr g)).mpr
    exact ⟨L.freeEdge g.val,L.free_paired g.val⟩
  | inr g =>
    apply (paired_right_iff L R fL fR (.inr g)).mpr
    exact ⟨R.freeEdge g.val,R.free_paired g.val⟩

/-- The actual finite open-network shape for disjoint free/free fusion.
Its local vertex arities and local coordinates are unchanged. -/
abbrev shape : FiniteShape (VL ⊕ VR) (CutFree fL ⊕ CutFree fR)
    (SpliceEdges L R fL fR) n where
  arity := SumArity L.arity R.arity
  boundary := (boundary L R fL fR i hL hR).trans (portSum L.arity R.arity).symm.toEmbedding
  ends := (ends L R fL fR).trans (portSum L.arity R.arity).symm.toEmbedding
  ordinary_boundary_iff_unpaired := by
    rintro ⟨v,k⟩
    cases v with
    | inl v =>
      change (∃ j,(portSum L.arity R.arity).symm (boundary L R fL fR i hL hR j) =
          (portSum L.arity R.arity).symm (.inl (.inl ⟨v,k⟩))) ↔
        ¬∃ eb,(portSum L.arity R.arity).symm (ends L R fL fR eb) =
          (portSum L.arity R.arity).symm (.inl (.inl ⟨v,k⟩))
      simp only [Equiv.apply_eq_iff_eq]
      rw [ordinary_boundary_left,paired_left_iff]
      exact L.ordinary_boundary_iff_unpaired ⟨v,k⟩
    | inr v =>
      change (∃ j,(portSum L.arity R.arity).symm (boundary L R fL fR i hL hR j) =
          (portSum L.arity R.arity).symm (.inr (.inl ⟨v,k⟩))) ↔
        ¬∃ eb,(portSum L.arity R.arity).symm (ends L R fL fR eb) =
          (portSum L.arity R.arity).symm (.inr (.inl ⟨v,k⟩))
      simp only [Equiv.apply_eq_iff_eq]
      rw [ordinary_boundary_right,paired_right_iff]
      exact R.ordinary_boundary_iff_unpaired ⟨v,k⟩
  freeBoundary := fun f => Classical.choose (free_boundary_exists L R fL fR i hL hR f)
  free_boundary := by
    intro f
    change (portSum L.arity R.arity).symm _ = _
    rw [Classical.choose_spec (free_boundary_exists L R fL fR i hL hR f)]
    exact (portSum L.arity R.arity).symm_apply_apply _
  freeEdge := fun f => Classical.choose (free_pair_exists L R fL fR f)
  free_paired := by
    intro f
    change (portSum L.arity R.arity).symm _ = _
    rw [Classical.choose_spec (free_pair_exists L R fL fR f)]
    exact (portSum L.arity R.arity).symm_apply_apply _

end Holant.OpenNetworkComposition.FreeFree
