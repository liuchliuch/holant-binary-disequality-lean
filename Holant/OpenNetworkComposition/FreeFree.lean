import Holant.OpenNetworkComposition.Finite

/-! Incidence-level deletion of one exposed free endpoint.  The opposite endpoint
is retained even when it is another free stub.  These definitions do not close a
wire-only component and introduce no vertex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition
namespace FiniteShape
variable {V F E : Type*} {n : ℕ}

abbrev CutFree (f : F) := {g : F // g ≠ f}
abbrev CutEdge (s : FiniteShape V F E n) (f : F) := {e : E // e ≠ (s.freeEdge f).1}
abbrev CutPorts (s : FiniteShape V F E n) (f : F) := Ports V (CutFree f) s.arity

def cutEmbed (s : FiniteShape V F E n) (f : F) : s.CutPorts f ↪ Ports V F s.arity where
  toFun := Sum.map id Subtype.val
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all
    exact Subtype.ext h

@[simp] theorem cutEmbed_inl (s : FiniteShape V F E n) (f : F) (p : Σ v, Fin (s.arity v)) :
    s.cutEmbed f (.inl p) = .inl p := rfl
@[simp] theorem cutEmbed_inr (s : FiniteShape V F E n) (f : F) (g : CutFree f) :
    s.cutEmbed f (.inr g) = .inr g.val := rfl

theorem cutEmbed_ne (s : FiniteShape V F E n) (f : F) (p : s.CutPorts f) :
    s.cutEmbed f p ≠ .inr f := by
  cases p with
  | inl p => simp
  | inr g => simpa using g.property

def cutPort (s : FiniteShape V F E n) (f : F) (p : Ports V F s.arity)
    (h : p ≠ .inr f) : s.CutPorts f :=
  match p with
  | .inl p => .inl p
  | .inr g => .inr ⟨g,fun hg => h (congrArg Sum.inr hg)⟩

@[simp] theorem cutEmbed_cutPort (s : FiniteShape V F E n) (f : F)
    (p : Ports V F s.arity) (h : p ≠ .inr f) :
    s.cutEmbed f (s.cutPort f p h) = p := by cases p <;> rfl

theorem retained_end_ne (s : FiniteShape V F E n) (f : F) (e : s.CutEdge f) (b : Bool) :
    s.ends (e.val,b) ≠ .inr f := by
  intro h
  have hh := s.ends.injective (h.trans (s.free_paired f).symm)
  exact e.property (congrArg Prod.fst hh)

def cutEnds (s : FiniteShape V F E n) (f : F) : (s.CutEdge f × Bool) ↪ s.CutPorts f where
  toFun eb := s.cutPort f (s.ends (eb.1.val,eb.2)) (s.retained_end_ne f eb.1 eb.2)
  inj' := by
    rintro ⟨e,b⟩ ⟨e',b'⟩ h
    have hmap := congrArg (s.cutEmbed f) h
    simp only [cutEmbed_cutPort] at hmap
    have hh := s.ends.injective hmap
    have he : e=e' := Subtype.ext (congrArg Prod.fst hh)
    have hb : b=b' := congrArg Prod.snd hh
    exact Prod.ext he hb

@[simp] theorem cutEmbed_cutEnds (s : FiniteShape V F E n) (f : F)
    (eb : s.CutEdge f × Bool) :
    s.cutEmbed f (s.cutEnds f eb) = s.ends (eb.1.val,eb.2) := by
  exact s.cutEmbed_cutPort f _ _

theorem opposite_ne (s : FiniteShape V F E n) (f : F) :
    s.ends ((s.freeEdge f).1,!(s.freeEdge f).2) ≠ .inr f := by
  intro h
  have hh := congrArg Prod.snd (s.ends.injective (h.trans (s.free_paired f).symm))
  exact Bool.not_ne_self _ hh

def cutOpposite (s : FiniteShape V F E n) (f : F) : s.CutPorts f :=
  s.cutPort f (s.ends ((s.freeEdge f).1,!(s.freeEdge f).2)) (s.opposite_ne f)

@[simp] theorem cutEmbed_cutOpposite (s : FiniteShape V F E n) (f : F) :
    s.cutEmbed f (s.cutOpposite f) = s.ends ((s.freeEdge f).1,!(s.freeEdge f).2) :=
  s.cutEmbed_cutPort f _ _

theorem cutEnds_ne_opposite (s : FiniteShape V F E n) (f : F)
    (eb : s.CutEdge f × Bool) : s.cutEnds f eb ≠ s.cutOpposite f := by
  intro h
  have hh := congrArg (s.cutEmbed f) h
  simp only [cutEmbed_cutEnds,cutEmbed_cutOpposite] at hh
  exact eb.1.property (congrArg Prod.fst (s.ends.injective hh))

/-- Every old paired endpoint which survives deletion is either on a retained
edge or is exactly the opposite endpoint of the removed edge. -/
theorem cut_paired_iff (s : FiniteShape V F E n) (f : F) (p : s.CutPorts f) :
    (∃ eb,s.ends eb=s.cutEmbed f p) ↔
      (∃ eb,s.cutEnds f eb=p) ∨ s.cutOpposite f=p := by
  classical
  constructor
  · rintro ⟨⟨e,b⟩,h⟩
    by_cases he : e=(s.freeEdge f).1
    · right
      apply (s.cutEmbed f).injective
      rw [cutEmbed_cutOpposite]
      have hb : b ≠ (s.freeEdge f).2 := by
        intro hb
        have hf : s.cutEmbed f p = .inr f := by
          rw [← h,he,hb]
          exact s.free_paired f
        exact s.cutEmbed_ne f p hf
      have hbn : b = !(s.freeEdge f).2 := by
        cases b <;> cases hf : (s.freeEdge f).2 <;> simp_all
      simpa [he,hbn] using h
    · left
      refine ⟨(⟨e,he⟩,b),?_⟩
      apply (s.cutEmbed f).injective
      simpa using h
  · rintro (⟨eb,h⟩|h)
    · exact ⟨(eb.1.val,eb.2),by rw [← cutEmbed_cutEnds, h]⟩
    · exact ⟨((s.freeEdge f).1,!(s.freeEdge f).2),by rw [← cutEmbed_cutOpposite,h]⟩

theorem boundary_ne_selected (s : FiniteShape V F E n) (f : F) (i : Fin n)
    (hi : s.boundary i=.inr f) (j : Fin n) (hj : j ≠ i) : s.boundary j ≠ .inr f := by
  intro h
  exact hj (s.boundary.injective (h.trans hi.symm))

def cutBoundary (s : FiniteShape V F E n) (f : F) (i : Fin n)
    (hi : s.boundary i=.inr f) : {j : Fin n // j ≠ i} ↪ s.CutPorts f where
  toFun j := s.cutPort f (s.boundary j.val) (s.boundary_ne_selected f i hi j.val j.property)
  inj' := by
    intro a b h
    apply Subtype.ext
    apply s.boundary.injective
    simpa only [cutEmbed_cutPort] using congrArg (s.cutEmbed f) h

@[simp] theorem cutEmbed_cutBoundary (s : FiniteShape V F E n) (f : F) (i : Fin n)
    (hi : s.boundary i=.inr f) (j : {j : Fin n // j ≠ i}) :
    s.cutEmbed f (s.cutBoundary f i hi j) = s.boundary j.val := s.cutEmbed_cutPort f _ _

end FiniteShape
end Holant.OpenNetworkComposition
