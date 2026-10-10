import Holant.Dihedral.CompatibleClosure.PhaseChoice
import Holant.Dihedral.CompatibleClosure.NativeCard

/-! Actual common-edge closure and two-edge cross-closure sums. Remainder
coefficients are arbitrary, so protected factors outside the operated ports are
preserved without any factor-availability assumption. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Tractable

/-- The actual binary placed between two native X-wires. -/
def connection (γ : Bool) (t : Scalar) : Mat :=
  Kernel.mul Signature.disequality (Kernel.mul (M γ t) Signature.disequality)

theorem connection_entry (γ : Bool) (t : Scalar) (a b : Bool) :
    connection γ t (!a) (!b) = M γ t a b := by
  rw [connection,Kernel.disequality_mul,Kernel.mul_disequality]
  simp

theorem connection_mem_group {m : ℕ} (hm : 0 < m) (γ : Bool) {t : Scalar} (ht : Roots m t) :
    connection γ t ∈ groupM m := by
  have hx : (Signature.disequality : Mat) ∈ groupM m := by
    refine ⟨1,Roots.one m,Or.inr ⟨1,one_ne_zero,?_⟩⟩
    funext a b
    simp [S,R_one,scale]
  exact groupM_mul hm hx (groupM_mul hm (M_mem_group hm γ ht) hx)

def close {n : ℕ} (γ : Bool) (t : Scalar) (q : Signature Scalar (n+2)) : Signature Scalar n :=
  fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b * q (Fin.cons a (Fin.cons b x))

theorem actual_close {n : ℕ} (γ : Bool) (t κ : Scalar) (q : Signature Scalar (n+2)) :
    nativeCardValue q (scale κ (connection γ t)) = κ • close γ t q := by
  funext x
  simp only [nativeCardValue,close,scale,connection_entry,Pi.smul_apply,smul_eq_mul,
    Fintype.sum_bool]
  ring

/-- One matching factor on the closed original pair; every other coefficient
remains in the ordered residual tensor R. -/
def commonProduct {n : ℕ} (α : Bool) (a : Scalar) (R : Signature Scalar n) : Signature Scalar (n+2) :=
  fun x => M α a (x 0) (x 1) * R (fun i => x i.succ.succ)

theorem close_common {n : ℕ} (α : Bool) (a t : Scalar) (R : Signature Scalar n) :
    close α t (commonProduct α a R) = (1+a*t) • R := by
  funext x
  change (∑ u : Bool, ∑ v : Bool, M α t u v * (M α a u v * R x)) = (1+a*t)*R x
  calc
    _ = trace (M α a) (M α t) * R x := by
      simp only [trace,Fintype.sum_bool]
      ring
    _ = _ := by rw [trace_M]

/-- Two incident factors before cross-closing u,v. Original surviving endpoints
r,s are the next two exposed ports, followed by the unchanged remainder. -/
def crossProduct {n : ℕ} (α β : Bool) (a b : Scalar) (R : Signature Scalar n) : Signature Scalar (n+4) :=
  fun x => M α a (x ((0 : Fin (n+2)).succ.succ)) (x 0) *
    M β b (x 1) (x ((1 : Fin (n+2)).succ.succ)) *
    R (fun i => x i.succ.succ.succ.succ)

theorem close_cross {n : ℕ} (α γ β : Bool) (a t b : Scalar) (R : Signature Scalar n) :
    close γ t (crossProduct α β a b R) =
      fun x => fuse (M γ t) (M α a) (M β b) (x 0) (x 1) *
        R (fun i => x i.succ.succ) := by
  funext x
  have hh (u v : Bool) : crossProduct α β a b R (Fin.cons u (Fin.cons v x)) =
      M α a (x 0) u * M β b v (x 1) * R (fun i => x i.succ.succ) := rfl
  simp only [close,hh,fuse,Signature.connect,Fintype.sum_bool]
  ring

/-- Literal cycle-shortening/cross-closure formula, including its nonzero
scalar and the final ordered phase. -/
theorem close_cross_normal_form {n : ℕ} (α γ β : Bool) (a t b : Scalar)
    (ht : t ≠ 0) (hb : b ≠ 0) (R : Signature Scalar n) :
    close γ t (crossProduct α β a b R) =
      (scalar α t * scalar (α ^^ γ) b) •
        commonProduct (α ^^ γ ^^ β) (a*exponent α t*exponent (α ^^ γ) b) R := by
  rw [close_cross,triple_fusion α γ β a t b ht hb]
  funext x
  simp only [commonProduct,scale,Pi.smul_apply,smul_eq_mul,mul_assoc]

/-- No nonzero common residual tensor becomes zero when the chosen trace is
nonzero. -/
theorem scalar_tensor_nonzero {n : ℕ} {c : Scalar} {R : Signature Scalar n}
    (hc : c ≠ 0) (hR : R ≠ 0) : c • R ≠ 0 := by
  intro hh
  apply hR
  funext x
  have he := congrFun hh x
  simpa only [Pi.smul_apply,smul_eq_mul,Pi.zero_apply,mul_eq_zero,hc,false_or] using he

theorem commonProduct_nonzero {n : ℕ} (α : Bool) (a : Scalar) {R : Signature Scalar n}
    (hR : R ≠ 0) : commonProduct α a R ≠ 0 := by
  intro hh
  apply hR
  funext x
  have he := congrFun hh (Fin.cons false (Fin.cons α x))
  simpa [commonProduct,M,monomial] using he

/-- The actual physical output of a cross-closure stays nonzero, and remains
an exact monomial product on its two surviving local endpoints. -/
theorem actual_cross_nonzero {n : ℕ} (α γ β : Bool) (a t b κ : Scalar)
    (ht : t ≠ 0) (hb : b ≠ 0) (hκ : κ ≠ 0) {R : Signature Scalar n} (hR : R ≠ 0) :
    nativeCardValue (crossProduct α β a b R) (scale κ (connection γ t)) ≠ 0 := by
  rw [actual_close,close_cross_normal_form α γ β a t b ht hb]
  exact scalar_tensor_nonzero hκ (scalar_tensor_nonzero (fusion_scalar_ne_zero α γ ht hb)
    (commonProduct_nonzero _ _ hR))

end Holant.Dihedral.CompatibleClosure
