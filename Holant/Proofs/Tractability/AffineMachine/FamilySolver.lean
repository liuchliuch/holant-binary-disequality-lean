import Holant.Proofs.Tractability.AffineMachine.WireCorrectness
import Holant.Proofs.Tractability.AffineMachine.AggregationRefinement


namespace Holant.LocalDrafts.Tractability.AffineMachine.FamilySolver

open Turing Computability Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open EncodedTable ProductMachine

noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ} (D : Assembly.Family s b arity)

def stateWidthPolynomial : Polynomial ℕ :=
  (WireSize.widthPolynomial s b).comp (BlockAggregation.fromRaw D).outputBound.bound

/-- Includes all padded physical rounds, not just the mathematically active
eliminations. The initial width comes from the actual aggregation machine. -/
theorem intermediate_bits (r : Input s b arity) (k : ℕ)
    (hk : k ≤ (WireRound.encoding.encode (RawMachine.initial D r)).length) :
    (WireRound.encoding.encode ((WireRound.step^[k]) (RawMachine.initial D r))).length ≤
      (stateWidthPolynomial D).eval (RawClosedNetwork.encoding.encode r.val).length := by
  have h := (BlockAggregation.fromRaw D).outputBound.length_le r
  have hi : (WireRound.encoding.encode (RawMachine.initial D r)).length ≤
      (BlockAggregation.fromRaw D).outputBound.bound.eval (RawClosedNetwork.encoding.encode r.val).length := h
  simpa only [stateWidthPolynomial, Polynomial.eval_comp] using
    WireSize.iterate_bits (RawMachine.initial D r) _ k hi (hk.trans hi)

theorem code_size (r : Input s b arity) :
    (RawMachine.code D r).size ≤ 6 * (RawClosedNetwork.encoding.encode r.val).length + 3 := by
  have h := WireCorrectness.output_size (RawMachine.initial D r)
  have he := RawCode.accumulator_size r
  rw [AggregationRefinement.accumulator] at h
  have hn : (RawMachine.initial D r).1.1 = 2 * r.val.edges.length := rfl
  rw [hn] at h
  have hc := RawClosedNetwork.counts_le_encoded_length r.val
  change (RawMachine.code D r).size ≤ _ at h
  omega

theorem code_bits (r : Input s b arity) :
    ((Expr.encoding FamilyField.labelEncoding).encode (RawMachine.code D r)).length ≤
      (2 * (FamilyField.labelCount (s := s) (b := b)).size + 14) *
        (6 * (RawClosedNetwork.encoding.encode r.val).length + 3) + 1 :=
  (WireSize.expression_width _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (code_size D r)) 1)

/-- Bound for the actually generated expression, not merely the old semantic
compiler's expression. It covers every common-field intermediate coordinate. -/
theorem coordinate_trace (r : Input s b arity) :
    ∀ x ∈ (RawMachine.code D r).trace
      (FieldInterpreter.coefficients (FamilyField.commonPresentation D) (FamilyField.coordinates D)),
      ∀ i, Holant.Algebraic.rationalBitHeight ((FamilyField.commonPresentation D).decode.symm x i) ≤
        FieldInterpreter.width (FamilyField.commonPresentation D) (FamilyField.coordinates D)
          (6 * (RawClosedNetwork.encoding.encode r.val).length + 3) :=
  (FieldInterpreter.coordinate_trace_bound (FamilyField.commonPresentation D)
    (FamilyField.coordinates D) _ _ (code_size D r)).2

theorem code_value (r : Input s b arity) :
    (RawMachine.code D r).eval (FamilyField.extra D) =
      (r.val.realize r.property D.signatures D.kernels).denote Fin.elim0 := by
  have he : (store (AggregationRefinement.table D r), (RawMachine.initial D r).2) =
      RawMachine.initial D r :=
    Prod.ext (ReadRefinement.store_restore _ (AggregationRefinement.regular D r)) rfl
  have h := WireCorrectness.partition_correct (RawCode.scale D)
    (AggregationRefinement.table D r) (RawMachine.initial D r).2
  rw [he] at h
  change (RawMachine.code D r).eval (FamilyField.extra D) =
    ((AggregationRefinement.table D r).state
      ((RawMachine.initial D r).2.eval (FamilyField.extra D))).partition at h
  rw [h, ← Assembly.global_partition D r]
  unfold State.partition
  exact Finset.sum_congr rfl (fun x _ => AggregationRefinement.table_value D r x)

theorem code_finiteCore_value (r : Input s b arity) :
    (RawMachine.code D r).eval (FamilyField.extra D) =
      (RawCode.expression D r).eval (FamilyField.extra D) := by
  rw [code_value, RawCode.expression_value]

/-- Membership in the original-field image follows from the original network
value, including zero/cancellation cases; it is not assumed for extra scales. -/
theorem common_embedding (r : Input s b arity) :
    (RawMachine.code D r).eval
      (FieldInterpreter.coefficients (FamilyField.commonPresentation D) (FamilyField.coordinates D)) =
        FamilyField.embedding D (FamilyField.originalValue D r) :=
  FamilyField.evaluation_embedding D (RawMachine.code D r) (FamilyField.originalValue D r)
    ((code_value D r).trans (FamilyField.originalValue_exact D r).symm)

theorem computedValue_exact (r : Input s b arity) :
    RawMachine.computedValue D r = FamilyField.originalValue D r := by
  rw [RawMachine.computedValue, common_embedding]
  exact Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recover_embed
    (FamilyField.originalCoefficient D) (FamilyField.extra D) (FamilyField.originalValue D r)

/-- No free Computes/Gaussian/PolyTimeOracleReduction argument. Both the
original value and answer codec are determined solely by the original tables. -/
def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (FamilyField.originalPresentation D).encoding (FamilyField.originalValue D) :=
  congrComputes (RawMachine.computes D) (computedValue_exact D)

theorem primitive_bound (r : Input s b arity) :
    primitiveCost (computes D).machine ((computes D).outputs r).steps
      (some (initList (computes D).machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial (computes D)).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes D) r

/-- The finite-family affine evaluation theorem. -/
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity)
    (FamilyField.originalPresentation D).encoding (FamilyField.originalValue D) := (computes D).inFP

end
end Holant.LocalDrafts.Tractability.AffineMachine.FamilySolver
