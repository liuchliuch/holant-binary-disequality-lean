import Holant.Dihedral.CompatibleCoefficientLine.Basic
import Holant.Dihedral.CompatibleClosure.SourceProtected

/-! A real finite-root choice for fusing two parity disagreements.  Neither
the surviving coefficient tag nor the actual connection phase is an input.
The selected phase works also at m = 3 and does not use a common nonzero
four-sample grid. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine

/-- The complete root grid cannot have one constant square when m ≥ 3.
We construct a root rather than assume a noncancelling phase. -/
theorem root_square_avoids {m : ℕ} (hm : 3 ≤ m) (d : Scalar) :
    ∃ t : {t : Scalar // Roots m t}, t.val ^ 2 ≠ d := by
  by_cases hd : d = 1
  · subst d
    obtain ⟨t,ht,hplus,hminus⟩ := simultaneous_phase hm 1 (-1)
      one_ne_zero (neg_ne_zero.mpr one_ne_zero)
    refine ⟨⟨t,ht⟩,?_⟩
    intro he
    have product : (1+t)*(1-t) = 0 := by linear_combination -he
    rcases mul_eq_zero.mp product with h | h
    · exact hplus (by simpa using h)
    · exact hminus (by simpa [sub_eq_add_neg] using h)
  · exact ⟨⟨1,by simp [Roots]⟩,by simpa using Ne.symm hd⟩

theorem factorDet_scale (p : Bool) (c d : Scalar) (A B : Mat) :
    factorDet p (scale c A) (scale d B) = (c*d)*factorDet p A B := by
  simp only [factorDet,scale]
  ring

theorem fuse_outer_scale (C A B : Mat) (c d : Scalar) :
    fuse C (scale c A) (scale d B) = scale (c*d) (fuse C A B) := by
  simp only [fuse_eq_mul,scale_mul_left,scale_mul_right]
  funext a b
  simp only [scale,mul_assoc]
  ring

/-- Literal determinant of the two fused tables.  The two changed support
parities cancel, but their coefficient ratio depends on the actual phase
square, so a genuine coefficient discrepancy can be retained. -/
theorem parity_pair_determinant (α β : Bool) (a₀ a₁ b₀ b₁ t : Scalar) :
    factorDet (α ^^ β)
      (fuse (M false t) (M α a₀) (M β b₀))
      (fuse (M false t) (M (!α) a₁) (M (!β) b₁)) =
      if α then a₁*b₀*b₁*t^2-a₀ else a₁-a₀*b₀*b₁*t^2 := by
  cases α <;> cases β <;>
    simp [factorDet,fuse_eq_mul,Kernel.mul_apply,M,monomial] <;> ring

/-- Two actual opposite-parity factor pairs have an internally chosen root
connection whose two resulting SAME-parity coefficient vectors differ. -/
theorem two_parity_discrepancies {m : ℕ} (hm : 3 ≤ m) (α β : Bool)
    (A₀ A₁ B₀ B₁ : Mat)
    (hA₀ : HasParity α A₀) (hA₁ : HasParity (!α) A₁)
    (hB₀ : HasParity β B₀) (hB₁ : HasParity (!β) B₁) :
    ∃ t : {t : Scalar // Roots m t},
      factorDet (α ^^ β) (fuse (M false t.val) A₀ B₀)
        (fuse (M false t.val) A₁ B₁) ≠ 0 := by
  obtain ⟨a₀,c₀,ha₀,hc₀,rfl⟩ := hA₀.normal_form
  obtain ⟨a₁,c₁,ha₁,hc₁,rfl⟩ := hA₁.normal_form
  obtain ⟨b₀,d₀,hb₀,hd₀,rfl⟩ := hB₀.normal_form
  obtain ⟨b₁,d₁,hb₁,hd₁,rfl⟩ := hB₁.normal_form
  have scaled (t : Scalar) :
      factorDet (α ^^ β)
        (fuse (M false t) (scale c₀ (M α a₀)) (scale d₀ (M β b₀)))
        (fuse (M false t) (scale c₁ (M (!α) a₁)) (scale d₁ (M (!β) b₁))) =
        ((c₀*d₀)*(c₁*d₁)) *
          (if α then a₁*b₀*b₁*t^2-a₀ else a₁-a₀*b₀*b₁*t^2) := by
    rw [fuse_outer_scale,fuse_outer_scale,factorDet_scale,parity_pair_determinant]
  cases α
  · obtain ⟨t,ht⟩ := root_square_avoids hm (a₁/(a₀*b₀*b₁))
    refine ⟨t,?_⟩
    rw [scaled]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero hc₀ hd₀) (mul_ne_zero hc₁ hd₁))
    intro h
    change a₁-a₀*b₀*b₁*t.val^2 = 0 at h
    apply ht
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero ha₀ hb₀) hb₁)).mpr
    linear_combination -h
  · obtain ⟨t,ht⟩ := root_square_avoids hm (a₀/(a₁*b₀*b₁))
    refine ⟨t,?_⟩
    rw [scaled]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero hc₀ hd₀) (mul_ne_zero hc₁ hd₁))
    intro h
    change a₁*b₀*b₁*t.val^2-a₀ = 0 at h
    apply ht
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero ha₁ hb₀) hb₁)).mpr
    linear_combination h

/-- Physical full-product fusion on the SAME literal residual matching.  The
phase and the nonzero fused discrepancy are derived; the actual optional
circle and representative multipliers stay in the returned PhysicalPair. -/
theorem physical_two_parity_discrepancies {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (p : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e f : Fin r) (distinct : e ≠ f) (α β : Bool)
    (he₀ : HasParity α (A₀ e)) (he₁ : HasParity (!α) (A₁ e))
    (hf₀ : HasParity β (A₀ f)) (hf₁ : HasParity (!β) (A₁ f))
    (actual₀ : Gadget.Realizes F .disequality (productValue p A₀ κ₀))
    (actual₁ : Gadget.Realizes F .disequality (productValue p A₁ κ₁)) :
    ∃ t : {t : Scalar // Roots m t},
      Nonempty (PhysicalPair F G (productValue p A₀ κ₀) (productValue p A₁ κ₁)
        (pairOrder (p (e,true)) (p (f,false))) false t) ∧
      factorDet (α ^^ β) (fuse (M false t.val) (A₀ e) (A₀ f))
        (fuse (M false t.val) (A₁ e) (A₁ f)) ≠ 0 := by
  obtain ⟨t,tag⟩ := two_parity_discrepancies hm α β _ _ _ _ he₀ he₁ hf₀ hf₁
  exact ⟨t,source_cross_closure hm F G p p A₀ A₁ hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁
    e f e f distinct distinct rfl rfl actual₀ actual₁ false t,tag⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
