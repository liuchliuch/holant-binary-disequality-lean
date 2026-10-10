import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Correctness
import Holant.Complexity.UniversalPairReduction.Surgery.PromisedValidation

/-! Validation refines the exact raw output without changing a single bit of
the emitted query or caller-context flag. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Turing Computability BinaryCompose FixedFieldMachines RawClosedNetwork
variable (s : ℕ) (arity : ℕ → ℕ)

/-- Complete native-X smoothing compiler, with a validated original-family
query and the explicit loop-component correction bit. -/
noncomputable def queryWithCircleComputes : Computes (inputEncoding s arity)
    (pairEncoding (validatedEncoding s 1 arity) encodingBoolBool)
    (fun r => (Surgery.query r,(Smoothing.compile s r.val).circle)) :=
  recode (computes s arity) id (fun _ => rfl) (fun _ => rfl)

noncomputable def queryComputes : Computes (inputEncoding s arity)
    (validatedEncoding s 1 arity) Surgery.query :=
  (queryWithCircleComputes s arity).andThen
    (Wiring.firstComputes (validatedEncoding s 1 arity) encodingBoolBool)

/-- The occurrence flag is read from the original stream, with the at-most-one
promise identifying positive occurrence with exactly one occurrence. -/
noncomputable def hasPairComputes : Computes (inputEncoding s arity) encodingBoolBool
    (fun r => decide (FixedGadgetSubstitution.occurrences s r.val=1)) :=
  congrComputes (presentComputes s arity) (fun r => by
    have h : FixedGadgetSubstitution.occurrences s r.val≠0 ↔
        FixedGadgetSubstitution.occurrences s r.val=1 := by
      have := r.property.2
      omega
    simp only [present,h])

noncomputable def circleFlagComputes : Computes (inputEncoding s arity) encodingBoolBool
    (fun r => (Smoothing.compile s r.val).circle) :=
  (computes s arity).andThen (Wiring.secondComputes encoding encodingBoolBool)

/-- Context for the oracle caller records the native-X circle scalar and whether
there is a distinguished occurrence at all. -/
noncomputable def queryWithFlagsComputes : Computes (inputEncoding s arity)
    (pairEncoding (validatedEncoding s 1 arity) (pairEncoding encodingBoolBool encodingBoolBool))
    (fun r => (Surgery.query r,((Smoothing.compile s r.val).circle,
      decide (FixedGadgetSubstitution.occurrences s r.val=1)))) :=
  pairComputes (queryComputes s arity)
    (pairComputes (circleFlagComputes s arity) (hasPairComputes s arity))

theorem query_inFP : InFP (inputEncoding s arity)
    (validatedEncoding s 1 arity) Surgery.query := (queryComputes s arity).inFP

theorem queryWithCircle_primitive_bound (r : Input s arity) :
    primitiveCost (queryWithCircleComputes s arity).machine
      ((queryWithCircleComputes s arity).outputs r).steps
      (some (initList (queryWithCircleComputes s arity).machine.computer
        ((inputEncoding s arity).encode r))) ≤
      (primitivePolynomial (queryWithCircleComputes s arity)).eval
        ((inputEncoding s arity).encode r).length :=
  computes_primitive_cost (queryWithCircleComputes s arity) r

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
