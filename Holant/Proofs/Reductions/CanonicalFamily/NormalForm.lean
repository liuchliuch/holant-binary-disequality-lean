import Holant.Proofs.FiniteGroups.Stabilization.CanonicalKeys
import Holant.Proofs.Reductions.RootPreprocessing.Retained
import Mathlib.Data.Finset.Sort


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.Tractable
open Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
attribute [local instance] Classical.propDecidable

theorem key_idempotent {K : Type*} [Field K] {n : ℕ} (f : Signature K n) :
    canonicalKey (canonicalKey f) = canonicalKey f := by
  by_cases hf : f = 0
  · simp [hf]
  · calc
      canonicalKey (canonicalKey f) = canonicalKey ((f (firstWord f hf))⁻¹ • f) :=
        congrArg canonicalKey (canonicalKey_of_ne_zero f hf)
      _ = canonicalKey f := canonicalKey_smul f _ (inv_ne_zero (firstWord_nonzero f hf))

theorem key_firstWord {K : Type*} [Field K] {n : ℕ}
    (f : Signature K n) (hf : f ≠ 0) :
    firstWord (canonicalKey f) (canonicalKey_nonzero f hf) = firstWord f hf := by
  have hs := firstWord_smul f hf (f (firstWord f hf))⁻¹
    (inv_ne_zero (firstWord_nonzero f hf))
  have word_congr {g h : Signature K n} (hg : g ≠ 0) (hh : h ≠ 0) (he : g = h) :
      firstWord g hg = firstWord h hh := by cases he; rfl
  exact (word_congr _ _ (canonicalKey_of_ne_zero f hf)).trans hs

theorem normalized_first_entry {K : Type*} [Field K] {n : ℕ}
    (f : Signature K n) (hf : f ≠ 0) :
    canonicalKey f (firstWord (canonicalKey f) (canonicalKey_nonzero f hf)) = 1 := by
  rw [key_firstWord]
  exact canonicalKey_pivot f hf

abbrev literalI : Signature AlgebraicComplex 2 :=
  Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature

theorem identity_pivot : literalI (firstWord literalI RootPreprocessing.identity_nonzero) = 1 := by
  have h := firstWord_nonzero literalI RootPreprocessing.identity_nonzero
  simp only [literalI,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,
    Signature.equality] at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem identity_key : canonicalKey literalI = literalI := by
  rw [canonicalKey_of_ne_zero literalI RootPreprocessing.identity_nonzero,identity_pivot]
  simp

end Holant.LocalDrafts.Hardness.CanonicalFamily
