import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.FieldSimp
import Holant.Realization
import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Max


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

noncomputable section
attribute [local instance] Classical.propDecidable
variable {L : Type*} [Field L] {n : ℕ}

private theorem signature_smul_ne_zero {c : L} {f : Signature L n}
    (hc : c ≠ 0) (hf : f ≠ 0) : c • f ≠ 0 := by
  intro h
  apply hf
  funext x
  exact (mul_eq_zero.mp (congrFun h x)).resolve_left hc

def orderedSupport (f : Signature L n) : Finset (Lex (Fin n → Bool)) := by
  classical
  exact Finset.univ.filter (fun x => f (ofLex x) ≠ 0)

theorem orderedSupport_nonempty (f : Signature L n) (hf : f ≠ 0) :
    (orderedSupport f).Nonempty := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  exact ⟨toLex x, by simpa [orderedSupport] using hx⟩

def firstWord (f : Signature L n) (hf : f ≠ 0) : Fin n → Bool :=
  ofLex ((orderedSupport f).min' (orderedSupport_nonempty f hf))

theorem firstWord_nonzero (f : Signature L n) (hf : f ≠ 0) : f (firstWord f hf) ≠ 0 := by
  have h := Finset.min'_mem (orderedSupport f) (orderedSupport_nonempty f hf)
  simpa [orderedSupport, firstWord] using h

/-- This is the actual first support entry, not an arbitrary pivot choice. -/
theorem firstWord_le (f : Signature L n) (hf : f ≠ 0) (x : Fin n → Bool) (hx : f x ≠ 0) :
    toLex (firstWord f hf) ≤ toLex x := by
  exact Finset.min'_le _ _ (by simpa [orderedSupport] using hx)

def canonicalKey (f : Signature L n) : Signature L n :=
  if hf : f = 0 then 0 else (f (firstWord f hf))⁻¹ • f

@[simp] theorem canonicalKey_zero : canonicalKey (0 : Signature L n) = 0 := by
  simp [canonicalKey]

theorem canonicalKey_of_ne_zero (f : Signature L n) (hf : f ≠ 0) :
    canonicalKey f = (f (firstWord f hf))⁻¹ • f := by simp [canonicalKey, hf]

theorem canonicalKey_nonzero (f : Signature L n) (hf : f ≠ 0) : canonicalKey f ≠ 0 := by
  rw [canonicalKey_of_ne_zero f hf]
  exact signature_smul_ne_zero (inv_ne_zero (firstWord_nonzero f hf)) hf

theorem canonicalKey_pivot (f : Signature L n) (hf : f ≠ 0) :
    canonicalKey f (firstWord f hf) = 1 := by
  rw [canonicalKey_of_ne_zero f hf]
  exact inv_mul_cancel₀ (firstWord_nonzero f hf)

theorem recover_from_key (f : Signature L n) (hf : f ≠ 0) :
    f = f (firstWord f hf) • canonicalKey f := by
  rw [canonicalKey_of_ne_zero f hf, smul_smul, mul_inv_cancel₀ (firstWord_nonzero f hf), one_smul]

theorem orderedSupport_smul (f : Signature L n) (c : L) (hc : c ≠ 0) :
    orderedSupport (c • f) = orderedSupport f := by
  classical
  ext x
  simp [orderedSupport, Pi.smul_apply, smul_eq_mul, hc]

theorem firstWord_smul (f : Signature L n) (hf : f ≠ 0) (c : L) (hc : c ≠ 0) :
    firstWord (c • f) (signature_smul_ne_zero hc hf) = firstWord f hf := by
  simp only [firstWord, orderedSupport_smul f c hc]

theorem canonicalKey_smul (f : Signature L n) (c : L) (hc : c ≠ 0) :
    canonicalKey (c • f) = canonicalKey f := by
  by_cases hf : f = 0
  · subst f
    simp
  · rw [canonicalKey_of_ne_zero _ (signature_smul_ne_zero hc hf), canonicalKey_of_ne_zero f hf,
      firstWord_smul f hf c hc]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    have hp := firstWord_nonzero f hf
    field_simp [hc, hp]

/-- Equal keys imply literal nonzero scalar equivalence of the input tables. -/
theorem eq_scalar_of_canonicalKey_eq (f g : Signature L n) (hf : f ≠ 0) (hg : g ≠ 0)
    (he : canonicalKey f = canonicalKey g) : ∃ c : L, c ≠ 0 ∧ f = c • g := by
  refine ⟨f (firstWord f hf) / g (firstWord g hg),
    div_ne_zero (firstWord_nonzero f hf) (firstWord_nonzero g hg), ?_⟩
  calc
    f = f (firstWord f hf) • canonicalKey f := recover_from_key f hf
    _ = f (firstWord f hf) • ((g (firstWord g hg))⁻¹ • g) := by
      rw [he, canonicalKey_of_ne_zero g hg]
    _ = (f (firstWord f hf) / g (firstWord g hg)) • g := by rw [smul_smul, div_eq_mul_inv]

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
