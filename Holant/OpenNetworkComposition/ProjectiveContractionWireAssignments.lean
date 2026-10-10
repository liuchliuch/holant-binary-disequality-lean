import Holant.OpenNetworkComposition.ProjectiveContractionWireShape

/-! Exact assignment bijection isolating both bits of a removed free/free wire. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Wire
variable {V F E : Type*} {m n : ℕ}
variable (s : FiniteShape V F E m) (f g : F)

/-- Restore precisely the two deleted free endpoint values. -/
def restore (z : Ports V (CutTwo f g) s.arity → Bool) (a b : Bool) (p : Ports V F s.arity) : Bool :=
  if hf : p=.inr f then a else if hg : p=.inr g then b else z (port s f g p hf hg)

@[simp] theorem restore_first (z : Ports V (CutTwo f g) s.arity → Bool) (a b : Bool) :
    restore s f g z a b (.inr f)=a := by simp [restore]

@[simp] theorem restore_second (hfg : f≠g) (z : Ports V (CutTwo f g) s.arity → Bool) (a b : Bool) :
    restore s f g z a b (.inr g)=b := by simp [restore,Ne.symm hfg]

@[simp] theorem restore_retained (z : Ports V (CutTwo f g) s.arity → Bool) (a b : Bool)
    (p : Ports V (CutTwo f g) s.arity) : restore s f g z a b (embed s f g p)=z p := by
  rw [restore,dite_eq_right (embed_ne_first s f g p),dite_eq_right (embed_ne_second s f g p)]
  apply congrArg z
  apply (embed s f g).injective
  simp

/-- All old assignments, including disconnected components, are enumerated once. -/
def assignmentEquiv (hfg : f≠g) :
    (Ports V F s.arity → Bool) ≃ (Bool × Bool × (Ports V (CutTwo f g) s.arity → Bool)) where
  toFun z := (z (.inr f),z (.inr g),fun p => z (embed s f g p))
  invFun p := restore s f g p.2.2 p.1 p.2.1
  left_inv := by
    intro z
    funext p
    by_cases hf : p=.inr f
    · subst p; simp
    by_cases hg : p=.inr g
    · subst p; simp [hfg]
    simp [restore,hf,hg]
  right_inv := by
    rintro ⟨a,b,z⟩
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp [hfg]
      · funext p; simp

variable (hop : s.ends ((s.freeEdge f).1,!(s.freeEdge f).2)=.inr g)
    (i j : Fin m) (hi : s.boundary i=.inr f) (hj : s.boundary j=.inr g)
    (β : Fin n ↪ Fin m) (hβ : ∀k,(∃l,β l=k) ↔ k≠i ∧ k≠j)

include hop in
theorem free_ne : f≠g := by
  intro hfg
  apply s.opposite_ne f
  rw [hop,hfg]

/-- The old full-boundary filter fixes the deleted bits and the retained word. -/
theorem restore_boundary_iff (hfg : f≠g) (z : Ports V (CutTwo f g) s.arity → Bool)
    (a b : Bool) (x : Fin m → Bool) :
    (∀k,restore s f g z a b (s.boundary k)=x k) ↔
      a=x i ∧ b=x j ∧ ∀k,z (boundary s f g i j hi hj β hβ k)=x (β k) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · simpa [hi] using h i
    · simpa [hj,hfg] using h j
    · intro k
      have hh := h (β k)
      rw [←embed_boundary s f g i j hi hj β hβ k,restore_retained] at hh
      exact hh
  · rintro ⟨ha,hb,h⟩ k
    by_cases hki : k=i
    · subst k; simpa [hi] using ha
    by_cases hkj : k=j
    · subst k; simpa [hj,hfg] using hb
    obtain ⟨l,hl⟩ := (hβ k).mpr ⟨hki,hkj⟩
    rw [←hl,←embed_boundary s f g i j hi hj β hβ l,restore_retained]
    exact h l

end Holant.OpenNetworkComposition.ProjectiveContraction.Wire
