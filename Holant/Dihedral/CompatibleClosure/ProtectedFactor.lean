import Holant.Dihedral.CompatibleClosure.ProductExtraction
import Holant.Dihedral.CompatibleClosure.PhysicalPair

/-! The protected determinant is tied to the literal untouched original binary
factor in an exact resulting coefficient product, rather than free parameters. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

variable {ι : Type*} [DecidableEq ι] {r : ℕ}

/-- The actual untouched factor after a cross-closure, with the overall input
and physical connection multipliers absorbed at that exact original factor. -/
def survivingFactor (δ κ : Scalar) (A : Mat) : Mat := scale (δ*κ) A

/-- Exact whole-output coefficient identity identifies the surviving factor
with the original indexed table. The full fused kernel retains its own scalar. -/
theorem cross_untouched_factor (p : (Fin r × Bool) ≃ ι) (A : Fin r → Mat) (δ κ : Scalar)
    (e f j : Fin r) (hef : e ≠ f) (hje : j ≠ e) (hjf : j ≠ f) (C : Mat) (x : ι → Bool) :
    δ * (∑ a : Bool, ∑ b : Bool, C a b *
      productValue p A κ (insertPair (p (e,true)) (p (f,false)) a b x)) =
      fuse C (A e) (A f) (x (p (e,false))) (x (p (f,true))) *
        survivingFactor δ κ (A j) (x (p (j,false))) (x (p (j,true))) *
        ∏ d ∈ ((Finset.univ.erase e).erase f).erase j, A d (x (p (d,false))) (x (p (d,true))) := by
  rw [close_product_two p A κ e f hef]
  have hj : j ∈ (Finset.univ.erase e).erase f := by simp [hje,hjf]
  have hp := (Finset.mul_prod_erase ((Finset.univ.erase e).erase f)
    (fun d => A d (x (p (d,false))) (x (p (d,true)))) hj).symm
  rw [hp]
  simp only [survivingFactor,scale]
  ring

/-- The analogous exact whole-output identity for a common-edge trace: the
literal untouched factor includes precisely the actual trace multiplier. -/
theorem common_untouched_factor (p : (Fin r × Bool) ≃ ι) (A : Fin r → Mat) (δ κ : Scalar)
    (e j : Fin r) (hje : j ≠ e) (C : Mat) (x : ι → Bool) :
    δ * (∑ a : Bool, ∑ b : Bool, C a b *
      productValue p A κ (insertPair (p (e,false)) (p (e,true)) a b x)) =
      survivingFactor (δ*trace (A e) C) κ (A j) (x (p (j,false))) (x (p (j,true))) *
        ∏ d ∈ ({e}ᶜ : Finset (Fin r)).erase j, A d (x (p (d,false))) (x (p (d,true))) := by
  rw [close_product_edge]
  have hj : j ∈ ({e}ᶜ : Finset (Fin r)) := by simp [hje]
  have hp := (Finset.mul_prod_erase ({e}ᶜ : Finset (Fin r))
    (fun d => A d (x (p (d,false))) (x (p (d,true)))) hj).symm
  rw [hp]
  simp only [survivingFactor,scale]
  ring

/-- Ordered entries of the actual source parity plane. -/
def factorDet (parity : Bool) (A B : Mat) : Scalar :=
  A false parity * B true (!parity) - A true (!parity) * B false parity

/-- The determinant uses the two literal original factor tables and their
literal updated tables appearing in cross_untouched_factor. -/
theorem surviving_factor_determinant (parity : Bool) (A B : Mat) (δ₀ δ₁ κ₀ κ₁ : Scalar) :
    factorDet parity (survivingFactor δ₀ κ₀ A) (survivingFactor δ₁ κ₁ B) =
      ((δ₀*κ₀)*(δ₁*κ₁))*factorDet parity A B := by
  simp only [factorDet,survivingFactor,scale]
  ring

theorem surviving_factor_determinant_nonzero (parity : Bool) (A B : Mat)
    {δ₀ δ₁ κ₀ κ₁ : Scalar} (hδ₀ : δ₀ ≠ 0) (hδ₁ : δ₁ ≠ 0) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (htag : factorDet parity A B ≠ 0) :
    factorDet parity (survivingFactor δ₀ κ₀ A) (survivingFactor δ₁ κ₁ B) ≠ 0 := by
  rw [surviving_factor_determinant]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hδ₀ hκ₀) (mul_ne_zero hδ₁ hκ₁)) htag

/-- Actual untouched original-factor entries retain their tag after the two
specific common-edge traces, including all original/physical multipliers. -/
theorem common_surviving_factor_tag (parity : Bool) (A B E H C : Mat)
    {δ₀ δ₁ κ₀ κ₁ : Scalar} (hδ₀ : δ₀ ≠ 0) (hδ₁ : δ₁ ≠ 0) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (htrace₀ : trace E C ≠ 0) (htrace₁ : trace H C ≠ 0) (htag : factorDet parity A B ≠ 0) :
    factorDet parity (survivingFactor (δ₀*trace E C) κ₀ A)
      (survivingFactor (δ₁*trace H C) κ₁ B) ≠ 0 :=
  surviving_factor_determinant_nonzero parity A B (mul_ne_zero hδ₀ htrace₀)
    (mul_ne_zero hδ₁ htrace₁) hκ₀ hκ₁ htag

/-- Same-family physical outputs give exactly the nonzero multipliers used
in the literal surviving original-factor tables above. -/
theorem PhysicalPair.surviving_factor_tag {m n : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {q₀ q₁ : Signature Scalar (n+2)} {order : Equiv.Perm (Fin (n+2))}
    {γ : Bool} {t : {t : Scalar // Roots m t}} (P : PhysicalPair F G q₀ q₁ order γ t)
    (parity : Bool) (A B : Mat) (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (htag : factorDet parity A B ≠ 0) :
    factorDet parity (survivingFactor (P.circle₀*G.multiplier γ t) κ₀ A)
      (survivingFactor (P.circle₁*G.multiplier γ t) κ₁ B) ≠ 0 :=
  surviving_factor_determinant_nonzero parity A B P.multiplier₀_nonzero P.multiplier₁_nonzero hκ₀ hκ₁ htag

end Holant.Dihedral.CompatibleClosure
