import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Assemble

/-! Every one of the m+1 required positive interpolation queries is compiled
from the original graph and a bounded index. Unary index length is charged to
the original faithful graph encoding, not to an expanded graph or a huge count.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.BoundedQueries
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable (s b : ℕ) (arity : ℕ → ℕ) (distinguished : ℕ)
abbrev Input := Σ r : FixedGadgetSubstitution.Compiler.Input s b arity,
  Fin (occurrences distinguished r.val + 1)

def inputEncoding := sigmaEncoding (validatedEncoding s b arity)
  (fun r => OccurrenceLabel.unaryPortEncoding (occurrences distinguished r.val + 1))

noncomputable def sourceComputes : Computes (inputEncoding s b arity distinguished)
    (validatedEncoding s b arity) (fun x => x.1) :=
  recode (Wiring.firstComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def indexComputes : Computes (inputEncoding s b arity distinguished)
    UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def value (label edge : ℕ) (x : Input s b arity distinguished) : RawClosedNetwork :=
  Occurrence.raw s b arity distinguished label edge (x.2.val,x.1)

/-- The same finite program works for every original graph and every sample
index 0≤k≤m; its physical chain length is t=k+1, so no zero-length gadget occurs. -/
noncomputable def computes (label edge : ℕ) : Computes (inputEncoding s b arity distinguished)
    encoding (value s b arity distinguished label edge) :=
  (pairComputes (indexComputes s b arity distinguished) (sourceComputes s b arity distinguished)).andThen
    (Occurrence.rawComputes s b arity distinguished label edge)

theorem index_le (x : Input s b arity distinguished) :
    x.2.val ≤ occurrences distinguished x.1.val := by omega

theorem length_positive (x : Input s b arity distinguished) : 0 < x.2.val + 1 := by omega

theorem sample_length_bound (x : Input s b arity distinguished) :
    x.2.val + 1 ≤ occurrences distinguished x.1.val + 1 := by omega

theorem input_length (x : Input s b arity distinguished) :
    ((inputEncoding s b arity distinguished).encode x).length =
      2 * ((validatedEncoding s b arity).encode x.1).length + 1 + x.2.val := by
  simp [inputEncoding,sigmaEncoding,OccurrenceLabel.unaryPortEncoding,
    Holant.Algebraic.frame_length]

theorem input_length_bound (x : Input s b arity distinguished) :
    ((inputEncoding s b arity distinguished).encode x).length ≤
      3 * ((validatedEncoding s b arity).encode x.1).length + 1 := by
  have hm := occurrences_le_input_length distinguished x.1.val
  have hk := index_le s b arity distinguished x
  rw [input_length]
  change occurrences distinguished x.1.val ≤ ((validatedEncoding s b arity).encode x.1).length at hm
  omega

noncomputable def originalTimePolynomial (label edge : ℕ) : Polynomial ℕ :=
  (computes s b arity distinguished label edge).time.comp (3 * Polynomial.X + 1)

theorem original_time_bound (label edge : ℕ) (x : Input s b arity distinguished) :
    ((computes s b arity distinguished label edge).outputs x).steps ≤
      (originalTimePolynomial s b arity distinguished label edge).eval
        ((validatedEncoding s b arity).encode x.1).length := by
  have ht := (computes s b arity distinguished label edge).outputs x |>.steps_le_m
  have hm := natPolynomial_eval_mono (computes s b arity distinguished label edge).time
    (input_length_bound s b arity distinguished x)
  simpa [originalTimePolynomial] using ht.trans hm

noncomputable def originalPrimitivePolynomial (label edge : ℕ) : Polynomial ℕ :=
  (primitivePolynomial (computes s b arity distinguished label edge)).comp (3 * Polynomial.X + 1)

theorem original_primitive_bound (label edge : ℕ) (x : Input s b arity distinguished) :
    primitiveCost (computes s b arity distinguished label edge).machine
      ((computes s b arity distinguished label edge).outputs x).steps
      (some (initList (computes s b arity distinguished label edge).machine.computer
        ((inputEncoding s b arity distinguished).encode x))) ≤
      (originalPrimitivePolynomial s b arity distinguished label edge).eval
        ((validatedEncoding s b arity).encode x.1).length := by
  have ht := computes_primitive_cost (computes s b arity distinguished label edge) x
  have hm := natPolynomial_eval_mono (primitivePolynomial (computes s b arity distinguished label edge))
    (input_length_bound s b arity distinguished x)
  simpa [originalPrimitivePolynomial] using ht.trans hm

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.BoundedQueries
