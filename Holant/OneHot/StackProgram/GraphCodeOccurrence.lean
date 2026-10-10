import Holant.OneHot.StackProgram.GraphCodeBounds

/-! Source-exact occurrence-local hypotheses. An unused fixed table entry need
not be one-hot or native-X; only labels occurring in the actual input matter. -/

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.Complexity.ExactSignatureTables

variable {s b : ℕ} {arity : ℕ → ℕ} {K : Type*} [CommSemiring K]
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (coeff : CoefficientIndex s b arity → K)

/-- Exact original-network value under hypotheses only on actual occurrences. -/
theorem labelledGraphCode_denote_of_occurrences
    (hf : ∀ v, Holant.Signature.OneHot (fun x => coeff (.inl ⟨r.signatureLabel h v, x⟩)))
    (hX : ∀ e, (fun x y => coeff (.inr (r.edgeLabel h e, x, y))) = Holant.Signature.disequality)
    (suffix : List K) :
    (run (interpretLabel coeff) (r.labelledGraphCode h) suffix).map Prod.fst =
      some ((r.realize h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y)))).denote Fin.elim0 :: suffix) := by
  rw [run_labelledGraphCode]
  simp only [Option.map_some]
  have hs := (r.executableRealize h (fun i x => coeff (.inl ⟨i, x⟩))
    (fun i x y => coeff (.inr (i, x, y)))).computedOneHotProgram_spec hf hX
  rw [hs.1, r.executableRealize_eq]

/-- Concrete emitted instruction count does not constrain unused table entries. -/
theorem labelledGraphCode_length_le_of_occurrences
    (hf : ∀ v, Holant.Signature.OneHot (fun x => coeff (.inl ⟨r.signatureLabel h v, x⟩)))
    (hX : ∀ e, (fun x y => coeff (.inr (r.edgeLabel h e, x, y))) = Holant.Signature.disequality) :
    (r.labelledGraphCode h).length ≤ 55 * (r.vertices.length + r.edges.length) + 1 :=
  length_computedGraphCode_le_graph (interpretLabel coeff) (r.labelNetwork h) none rfl hf hX

/-- The same occurrence-local version bounds actual serialized output syntax. -/
theorem labelledGraphCode_encoded_length_le_of_occurrences
    (hf : ∀ v, Holant.Signature.OneHot (fun x => coeff (.inl ⟨r.signatureLabel h v, x⟩)))
    (hX : ∀ e, (fun x y => coeff (.inr (r.edgeLabel h e, x, y))) = Holant.Signature.disequality) :
    ((codeEncoding (treeLabelEncoding s b arity)).encode (r.labelledGraphCode h)).length ≤
      (2 * lengthBound s b arity + 14) *
        (55 * (RawClosedNetwork.encoding.encode r).length + 1) + 1 := by
  have hc := r.labelledGraphCode_length_le_of_occurrences h coeff hf hX
  have hs := r.decoded_counts_le_input_length h
  change r.vertices.length + r.edges.length ≤ (RawClosedNetwork.encoding.encode r).length at hs
  have he := codeEncoding_length_le (treeLabelEncoding s b arity) (lengthBound s b arity)
    (treeLabelEncoding_length_le s b arity) (r.labelledGraphCode h)
  have hn : (r.labelledGraphCode h).length ≤
      55 * (RawClosedNetwork.encoding.encode r).length + 1 := by omega
  exact he.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left (2 * lengthBound s b arity + 14) hn) 1)

end Holant.Complexity.RawClosedNetwork
