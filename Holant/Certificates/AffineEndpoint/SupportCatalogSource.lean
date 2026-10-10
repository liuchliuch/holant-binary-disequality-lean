import Holant.Certificates.AffineEndpoint.SupportCatalog
import Mathlib.Data.Nat.Size

/-! Canonical origin, basis and original-port correspondence with the source
verifier's integer-word charts. -/
namespace Holant.Certificates.AffineEndpoint.SupportCatalog
open Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def orderedCodes (S : Finset (Fin 16)) : List (Fin 16) :=
  (List.finRange 16).filter (fun a => decide (a ∈ S))

def supportBasis (s : SupportIndex) (j : Fin (supportDim s)) : Word 4 :=
  codeWord ((linearRows (supportLinearIndex s)).generators j)

theorem source_word_port_order : ∀ a : Fin 16, ∀ p : Fin 4,
    codeWord a p = a.val.testBit (3 - p.val) := by decide +kernel

theorem source_linear_dimension : ∀ l : LinearIndex,
    Nat.size ((linearRows l).codes.card - 1) = linearDim l := by decide +kernel

theorem source_basis_nondegenerate : ∀ l : LinearIndex,
    (∀ j, (linearRows l).generators j ≠ 0) ∧
      (∀ j k, j < k → (linearRows l).generators j < (linearRows l).generators k) := by
  decide +kernel

theorem source_linear_order : ∀ i : Fin 66,
    (linearRows i.castSucc).codes.card < (linearRows i.succ).codes.card ∨
      ((linearRows i.castSucc).codes.card = (linearRows i.succ).codes.card ∧
        List.Lex (· < ·) (orderedCodes (linearRows i.castSucc).codes)
          (orderedCodes (linearRows i.succ).codes)) := by
  decide +kernel

theorem source_support_order : ∀ i : Fin 306,
    (supportRows i.castSucc).linearIndex < (supportRows i.succ).linearIndex ∨
      ((supportRows i.castSucc).linearIndex = (supportRows i.succ).linearIndex ∧
        List.Lex (· < ·) (orderedCodes (supportRows i.castSucc).codes)
          (orderedCodes (supportRows i.succ).codes)) := by
  decide +kernel

theorem support_mask_membership : ∀ s : SupportIndex, ∀ a : Fin 16,
    (supportRows s).mask.val.testBit a.val = true ↔ a ∈ (supportRows s).codes := by
  decide +kernel

theorem supportChart_basis (s : SupportIndex) (j : Fin (supportDim s)) :
    supportChart s (basis j) = xor (supportOrigin s) (supportBasis s j) := by
  unfold supportChart
  congr 1
  funext p
  apply bitValue_injective
  change bitValue (ZMod 2) (matrixWord (generatorMatrix (supportLinearIndex s)) (basis j) p) = _
  rw [matrixWord, bitValue_binaryBool]
  change TwoTranslate.dot (generatorMatrix (supportLinearIndex s) p) (basis j) = _
  rw [dot_basis]
  rfl

theorem support_direction (s : SupportIndex) :
    translateSet (supportOrigin s) (supportWords s) = linearWords (supportLinearIndex s) := by
  rw [supportWords_translate, translateSet_twice]

theorem support_basis_spans_direction (s : SupportIndex) :
    decodeSupport (codeSpan (List.ofFn (linearRows (supportLinearIndex s)).generators)) =
      translateSet (supportOrigin s) (supportWords s) := by
  rw [linear_basis_spans, support_direction]
  rfl

theorem support_source_dimension (s : SupportIndex) :
    Nat.size ((supportWords s).card - 1) = supportDim s := by
  rw [supportWords_card]
  have h := source_linear_dimension (supportLinearIndex s)
  rw [linear_codes_card] at h
  exact h

end Holant.Certificates.AffineEndpoint.SupportCatalog
