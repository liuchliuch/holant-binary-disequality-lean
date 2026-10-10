import Holant.Pauli.ExoticKlein.SixPortAtlasScales
import Holant.Pauli.ExoticKlein.SixPortAtlasDirections

/-! Complete statement of source Proposition A.12. These clauses are proved
from the literal matrices, actual card semantics and the exhaustive product
classification; the record is a theorem output, never an atlas hypothesis. -/
namespace Holant.Pauli.ExoticKlein.Certificate
noncomputable section
open SixPort SixPort.Atlas

structure SixPortClause : Prop where
  direction_count : Fintype.card Direction = 48
  direction_nonzero : ∀ i : Fin 48, directionTensor (directionEquiv i) ≠ 0
  direction_distinct : ∀ i j : Fin 48, ∀ c : ℂ,
    directionTensor (directionEquiv i) = (fun x => c*directionTensor (directionEquiv j) x) → i = j
  direction_complete : ∀ h : Signature ℂ 4, h ≠ 0 →
    (h = 0 ∨ ∃ M : Matching (Fin 4) 2, ∃ labels : Fin 2 → Label, ∃ c : ℂ,
      c ≠ 0 ∧ h = fun x => c*M.tensor labels x) →
    ∃ i : Fin 48, ∃ c : ℂ, c ≠ 0 ∧ h = fun x => c*directionTensor (directionEquiv i) x
  state_count : Fintype.card DirectionTriple = 117649
  exact_line_count : Nat.card {h : Signature ℂ 6 // NormalizedSafe h} = 17
  exact_scales : ∀ h : Signature ℂ 6, NormalizedSafe h ↔ h = singleTensor ∨
    ∃ g : Fin 4, ∃ eps delta : Bool, h = signedTensor g eps delta
  actual_survivors : ∀ i : Fin 17, NormalizedSafe (candidate i) ∧ IsProduct (candidate i)
  projective_distinct : ∀ i j : Fin 17, ∀ c : ℂ,
    (fun x => c*candidate i x) = candidate j → i = j
  one_card_count : (Finset.univ.filter (fun i : Fin 17 => (liveCards i).card = 1)).card = 1
  four_card_count : (Finset.univ.filter (fun i : Fin 17 => (liveCards i).card = 4)).card = 16
  actual_card_support : ∀ i : Fin 17, ∀ a : Fin 4,
    a ∈ liveCards i ↔ baseCard (labelEquiv a) (candidate i) ≠ 0

theorem six_port_clause : SixPortClause where
  direction_count := SixPort.direction_count
  direction_nonzero := Atlas.direction_nonzero
  direction_distinct := directions_projectively_distinct
  direction_complete := directions_complete
  state_count := direction_triple_count
  exact_line_count := normalized_safe_card
  exact_scales := normalized_safe_explicit_iff
  actual_survivors i := ⟨candidate_safe i,candidate_product i⟩
  projective_distinct := candidate_projective_distinct
  one_card_count := one_card_line_count
  four_card_count := four_card_line_count
  actual_card_support := mem_liveCards_iff

structure EightPortClause : Prop where
  context_count : Fintype.card EightPort.CardContext = 112
  proper_factor : ∀ h : Signature ℂ 8, ∀ lambda : Label → ℂ,
    ∀ A1 A2 A3 : Label ≃ₗ[ZMod 2] Label,
      h = EightPort.normalForm lambda A1.toAddEquiv A2.toAddEquiv A3.toAddEquiv →
      (∀ a, lambda a ≠ 0) → EightPort.AllSafeCards h → EightPort.HasProperTensorFactor h

theorem eight_port_clause : EightPortClause where
  context_count := EightPort.card_context_count
  proper_factor := EightPort.eight_port_linear_has_proper_tensor_factor

/-- Proposition A.12, both finite clauses, including the exact17-line count,
literal signed half-scales, all zero/cancellation loci, and the112-card
eight-port conclusion with its actual normal form and nonzero coefficients. -/
theorem exotic_klein_six_eight_certificate : SixPortClause ∧ EightPortClause :=
  ⟨six_port_clause,eight_port_clause⟩

end
end Holant.Pauli.ExoticKlein.Certificate
