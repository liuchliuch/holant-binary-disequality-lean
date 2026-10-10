import Holant.Dihedral.CompatibleClosure.ProductExtraction
import Holant.Dihedral.CompatibleClosure.Contractions

/-! The full-original-word contraction is exactly the actual smaller signature
in any explicit residual port order. Nonvanishing transfers without a supplied
support certificate or an arity-changing semantic oracle. -/
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

variable {n : ℕ}

theorem insertPair_order (p : Equiv.Perm (Fin (n+2))) (a b : Bool) (x : Fin (n+2) → Bool) :
    insertPair (p 0) (p 1) a b x =
      fun i => (Fin.cons a (Fin.cons b (fun j => x (p j.succ.succ))) : Fin (n+2) → Bool) (p.symm i) := by
  have h01 : p 0 ≠ p 1 := fun h => Fin.zero_ne_one (p.injective h)
  funext i
  obtain ⟨j,rfl⟩ := p.surjective i
  simp only [Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
  · exact insertPair_first h01 a b x
  · exact insertPair_second _ _ a b x
  · have h0 : p k.succ.succ ≠ p 0 := fun h => Fin.succ_ne_zero k.succ (p.injective h)
    have h1 : p k.succ.succ ≠ p 1 := fun h => Fin.succ_succ_ne_one k (p.injective h)
    exact insertPair_other h0 h1 a b x

/-- Exact residual-coordinate bridge for the same original selected endpoints. -/
theorem full_close_order (p : Equiv.Perm (Fin (n+2))) (q : Signature Scalar (n+2))
    (γ : Bool) (t : Scalar) (x : Fin (n+2) → Bool) :
    (∑ a : Bool, ∑ b : Bool, M γ t a b * q (insertPair (p 0) (p 1) a b x)) =
      close γ t (Tensor.reindex p.symm q) (fun j => x (p j.succ.succ)) := by
  simp only [close,Tensor.reindex,insertPair_order]

/-- A nonzero full-word contraction gives a nonzero actual signature on exactly
n surviving original ports. -/
theorem full_close_nonzero (p : Equiv.Perm (Fin (n+2))) (q : Signature Scalar (n+2))
    (γ : Bool) (t : Scalar)
    (h : (fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b * q (insertPair (p 0) (p 1) a b x)) ≠ 0) :
    close γ t (Tensor.reindex p.symm q) ≠ 0 := by
  intro hz
  apply h
  funext x
  rw [full_close_order,hz]
  rfl

end Holant.Dihedral.CompatibleClosure
