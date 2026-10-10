import Holant.Proofs.Tractability.AffineMachine.WireLoop


namespace Holant.LocalDrafts.Tractability.AffineMachine.RawMachine

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler ProductMachine

variable {s b : ℕ} {arity : ℕ → ℕ} (D : Assembly.Family s b arity)

noncomputable def initial (r : Input s b arity) :=
  BlockAggregation.value (2 * r.val.edges.length, RawBlocks.blocks D r)

noncomputable def code (r : Input s b arity) := WireRound.finish (WireLoop.value (initial D r))

noncomputable def codeComputes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (Expr.encoding (FamilyField.labelEncoding (s := s) (b := b))) (code D) :=
  ((BlockAggregation.fromRaw D).andThen WireLoop.fromState).andThen WireRound.finishComputes

noncomputable def computedValue (r : Input s b arity) :=
  FamilyField.recover D ((code D r).eval
    (FieldInterpreter.coefficients (FamilyField.commonPresentation D) (FamilyField.coordinates D)))

noncomputable def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (FamilyField.originalPresentation D).encoding (computedValue D) :=
  (codeComputes D).andThen (FamilyField.codeComputes D)

/-- The cost starts at original graph bytes, and includes all table accesses,
list traversal, framing, loop control, scalar interpretation and recovery. -/
theorem primitive_bound (r : Input s b arity) :
    primitiveCost (computes D).machine ((computes D).outputs r).steps
      (some (initList (computes D).machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial (computes D)).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes D) r

theorem generated_state_terminal (r : Input s b arity) : (WireLoop.value (initial D r)).1.1 = 0 :=
  WireLoop.terminal _

end Holant.LocalDrafts.Tractability.AffineMachine.RawMachine
