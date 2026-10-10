import Holant.ReedMuller.TwoChart.GeometryDiagonal

/-! Nonalternating nondegenerate binary symmetric spaces have literal
standard-dot coordinates, given by a finite linear equivalence. -/
namespace Holant.ReedMuller.TwoChart.Geometry
open Module
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module F₂ V]

def consLinearEquiv (n : ℕ) : (F₂ × BinaryVector n) ≃ₗ[F₂] BinaryVector (n + 1) where
  toFun av := Fin.cons av.1 av.2
  invFun v := (v 0, Fin.tail v)
  left_inv := by rintro ⟨a, v⟩; rfl
  right_inv := by intro v; exact Fin.cons_self_tail v
  map_add' := by
    rintro ⟨a, v⟩ ⟨b, w⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' := by
    rintro a ⟨b, v⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem dot_cons (n : ℕ) (a b : F₂) (v w : BinaryVector n) :
    dot (consLinearEquiv n (a, v)) (consLinearEquiv n (b, w)) = a * b + dot v w := by
  simp [dot, consLinearEquiv, Fin.sum_univ_succ]

def lineSumEquiv (B : LinearMap.BilinForm F₂ V) (x : V) (hx : B x x = 1) :
    (F₂ × B.orthogonal (Submodule.span F₂ {x})) ≃ₗ[F₂] V :=
  ((LinearEquiv.toSpanNonzeroSingleton F₂ V x (by intro h; simp [h] at hx)).prodCongr
    (LinearEquiv.refl F₂ _)).trans
      (Submodule.prodEquivOfIsCompl _ _
        (B.isCompl_span_singleton_orthogonal (by rw [hx]; decide)))

@[simp] theorem lineSumEquiv_apply (B : LinearMap.BilinForm F₂ V)
    (x : V) (hx : B x x = 1)
    (a : F₂) (p : B.orthogonal (Submodule.span F₂ {x})) :
    lineSumEquiv B x hx (a, p) = a • x + p := rfl

theorem lineSumEquiv_form (B : LinearMap.BilinForm F₂ V) (hB : B.IsSymm)
    (x : V) (hx : B x x = 1) (a b : F₂)
    (p q : B.orthogonal (Submodule.span F₂ {x})) :
    B (lineSumEquiv B x hx (a, p)) (lineSumEquiv B x hx (b, q)) =
      a * b + B (p : V) q := by
  have hxp : B x (p : V) = 0 := p.property x (Submodule.subset_span (by simp))
  have hxq : B x (q : V) = 0 := q.property x (Submodule.subset_span (by simp))
  have hpx : B (p : V) x = 0 := (hB.eq p x).trans hxp
  simp [hx, hpx, hxq]

variable [FiniteDimensional F₂ V]

theorem exists_standard_coordinates_aux (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate)
    (ha : finrank F₂ V = 0 ∨ ∃ x : V, B x x = 1) :
    ∃ n : ℕ, ∃ e : V ≃ₗ[F₂] BinaryVector n, ∀ x y, dot (e x) (e y) = B x y := by
  generalize hd : finrank F₂ V = d at *
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
    by_cases hz : d = 0
    · have hv : finrank F₂ V = 0 := hd.trans hz
      have : Subsingleton V := finrank_zero_iff.mp hv
      let e : V ≃ₗ[F₂] BinaryVector 0 := LinearEquiv.ofFinrankEq _ _ (by simpa using hv)
      refine ⟨0, e, ?_⟩
      intro x y
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx, dot]
    obtain ⟨x, hx, hrest⟩ := exists_anisotropic_split B hB hn
      (ha.resolve_left hz)
    let P := B.orthogonal (Submodule.span F₂ {x})
    have hx0 : x ≠ 0 := by intro h; simp [h] at hx
    have hdP : 1 + finrank F₂ P = d := by
      simpa [finrank_span_singleton hx0, hd] using
        finrank_add_orthogonal B hn (Submodule.span F₂ {x})
    have hnP : (B.restrict P).Nondegenerate :=
      B.restrict_nondegenerate_orthogonal_spanSingleton hn hB.isRefl (by rw [hx]; decide)
    obtain ⟨m, f, hf⟩ := ih (finrank F₂ P) (by omega)
      (B.restrict P) (hB.restrict P) hnP rfl hrest
    let split := lineSumEquiv B x hx
    let e : V ≃ₗ[F₂] BinaryVector (m + 1) :=
      split.symm.trans (((LinearEquiv.refl F₂ F₂).prodCongr f).trans (consLinearEquiv m))
    refine ⟨m + 1, e, ?_⟩
    intro u v
    obtain ⟨⟨a, p⟩, rfl⟩ := split.surjective u
    obtain ⟨⟨b, q⟩, rfl⟩ := split.surjective v
    have heu : e (split (a, p)) = consLinearEquiv m (a, f p) := by
      simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rfl
    have hev : e (split (b, q)) = consLinearEquiv m (b, f q) := by
      simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rfl
    rw [heu, hev, dot_cons, hf]
    exact (lineSumEquiv_form B hB x hx a b p q).symm

/-- Classification in the form needed for an actual physical boundary:
the isometry is a linear equivalence to standard coordinate dot. -/
theorem exists_standard_dot_isometry (B : LinearMap.BilinForm F₂ V)
    (hB : B.IsSymm) (hn : B.Nondegenerate) (ha : ∃ x : V, B x x = 1) :
    ∃ e : V ≃ₗ[F₂] BinaryVector (finrank F₂ V),
      ∀ x y, dot (e x) (e y) = B x y := by
  obtain ⟨n, e, he⟩ := exists_standard_coordinates_aux B hB hn (Or.inr ha)
  have hd : finrank F₂ V = n := by simpa [BinaryVector] using e.finrank_eq
  subst n
  exact ⟨e, he⟩

end
end Holant.ReedMuller.TwoChart.Geometry
