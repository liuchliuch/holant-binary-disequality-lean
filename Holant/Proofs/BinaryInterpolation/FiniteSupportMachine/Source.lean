import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.Loop


namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Source

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing

theorem decoded_value (d : Codec.Matrix) :
    Controller.answer (Loop.value (Controller.initial d)) = Semantics.solve d := by
  apply ControllerSemantics.answer_iterate
  have h := Storage.measure_le_bytes (Controller.initial d)
  simpa only [ControllerSemantics.initial_measure] using h

/-- Actual encoded ordinary machine, with no oracle and no supplied witness. -/
noncomputable def computes : Computes Codec.encoding Controller.outputEncoding Semantics.solve :=
  congrComputes ((Controller.initialComputes.andThen Loop.fromState).andThen Controller.answerComputes)
    decoded_value

theorem inFP : InFP Codec.encoding Controller.outputEncoding Semantics.solve := computes.inFP

theorem output_faithful (w : Option (List Bool)) :
    Controller.outputEncoding.decode (Controller.outputEncoding.encode w) = some w :=
  Controller.outputEncoding.decode_encode w

theorem sound (d : Codec.Matrix) (w : List Bool) (h : Semantics.solve d = some w) :
    w.length = d.1 ∧ (Codec.support d).Holds (fun j => w.getD j.val false) :=
  Semantics.solve_sound d w h

theorem none_iff (d : Codec.Matrix) :
    Semantics.solve d = none ↔ ¬ ∃ x, (Codec.support d).Holds x := Semantics.solve_none_iff d

theorem time_bound (d : Codec.Matrix) :
    (computes.outputs d).steps ≤ computes.time.eval (Codec.encoding.encode d).length :=
  (computes.outputs d).steps_le_m

theorem primitive_bound (d : Codec.Matrix) :
    primitiveCost computes.machine (computes.outputs d).steps
      (some (initList computes.machine.computer (Codec.encoding.encode d))) ≤
        (primitivePolynomial computes).eval (Codec.encoding.encode d).length :=
  computes_primitive_cost computes d

/-- This polynomial measures storage in ORIGINAL matrix-input bits, including
the normalization program's generated rectangular table and control framing. -/
noncomputable def intermediatePolynomial : Polynomial ℕ :=
  Storage.widthPolynomial.comp Controller.initialComputes.outputBound.bound

theorem intermediate_bound (d : Codec.Matrix) (k : ℕ)
    (hk : k ≤ (Controller.encoding.encode (Controller.initial d)).length) :
    (Controller.encoding.encode ((Controller.step^[k]) (Controller.initial d))).length ≤
      intermediatePolynomial.eval (Codec.encoding.encode d).length := by
  have hi := Controller.initialComputes.outputBound.length_le d
  have h := Storage.iterate_bytes (Controller.initial d)
    (Controller.initialComputes.outputBound.bound.eval (Codec.encoding.encode d).length) k hi (hk.trans hi)
  simpa only [intermediatePolynomial, Polynomial.eval_comp] using h

/-- A single polynomial for transitions, primitive instructions and stored
round boundaries. Provider-internal temporary tapes are bounded separately
by the whole-machine run_size_le theorem below. -/
noncomputable def resourcePolynomial : Polynomial ℕ :=
  computes.time + primitivePolynomial computes + intermediatePolynomial +
    Polynomial.X + computes.time * Polynomial.C computes.machine.primitiveBudget

theorem intermediate_resource_bound (d : Codec.Matrix) (k : ℕ)
    (hk : k ≤ (Controller.encoding.encode (Controller.initial d)).length) :
    (Controller.encoding.encode ((Controller.step^[k]) (Controller.initial d))).length ≤
      resourcePolynomial.eval (Codec.encoding.encode d).length := by
  have h := intermediate_bound d k hk
  simp only [resourcePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

theorem resource_bound (d : Codec.Matrix) :
    (computes.outputs d).steps ≤ resourcePolynomial.eval (Codec.encoding.encode d).length ∧
    primitiveCost computes.machine (computes.outputs d).steps
      (some (initList computes.machine.computer (Codec.encoding.encode d))) ≤
        resourcePolynomial.eval (Codec.encoding.encode d).length := by
  have ht := time_bound d
  have hp := primitive_bound d
  simp only [resourcePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  constructor <;> omega

/-- Covers scratch tapes inside row lookup, frame copying, scans and parity
programs as well as visible round boundaries. The only premise describes an
actual reachable machine configuration at a bounded run prefix. -/
theorem runtime_storage (d : Codec.Matrix) (t : ℕ) (c : computes.machine.Config)
    (ht : t ≤ (computes.outputs d).steps)
    (hc : (fun p => p.bind computes.machine.computer.step)^[t]
      (some (initList computes.machine.computer (Codec.encoding.encode d))) = some c) :
    stackSize c.stk ≤ resourcePolynomial.eval (Codec.encoding.encode d).length := by
  have hs := computes.machine.run_size_le
    (initList computes.machine.computer (Codec.encoding.encode d)) c t hc
  rw [Machine.size_init] at hs
  have ht' := ht.trans (time_bound d)
  have hm := Nat.mul_le_mul_right computes.machine.primitiveBudget ht'
  simp only [resourcePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Source
