import Holant.Proofs.Tractability.ProductMachine.StateSize
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateFinish


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.ProductMachine.Loop

open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open StackProtocol

def inputEncoding : Encoding Round.State Bool where
  encode s := frame (Round.encoding.encode s)
  decode bits := do
    let (word, rest) ← unframe bits
    if rest = [] then Round.encoding.decode word else none
  decode_encode s := by
    have hf : unframe (frame (Round.encoding.encode s)) = some (Round.encoding.encode s, []) := by
      simpa only [List.append_nil] using unframe_frame_append (Round.encoding.encode s) []
    rw [hf]
    simp


noncomputable def provider :
    Computes (pairEncoding Round.encoding Frame.wordEncoding) Round.encoding (fun x => Round.step x.1) :=
  (Wiring.firstComputes Round.encoding Frame.wordEncoding).andThen Round.computes

noncomputable def machine := BitmapIterate.machine provider.machine

noncomputable def roundPolynomial : Polynomial ℕ :=
  provider.time.comp (2 * StateSize.widthPolynomial + 1) + 7 * StateSize.widthPolynomial + 11

noncomputable def timePolynomial : Polynomial ℕ :=
  5 * Polynomial.X + 8 + Polynomial.X * roundPolynomial + 2 * StateSize.widthPolynomial + 5

def value (s : Round.State) := (Round.step^[s.1]) s

theorem loop_run (s : Round.State) (N : ℕ) (hs : (Round.encoding.encode s).length ≤ N)
    (k i : ℕ) (hki : i + k ≤ N) :
    ∃ time, time ≤ k * roundPolynomial.eval N ∧
      RunsExactly machine.computer.step
        (BitmapIterate.ready provider.machine (BitmapIterate.phase provider.machine 5)
          (Round.encoding.encode ((Round.step^[i]) s)) [] (List.replicate k true) [] [] [])
        (BitmapIterate.ready provider.machine (BitmapIterate.phase provider.machine 5)
          (Round.encoding.encode ((Round.step^[i + k]) s)) [] [] [] [] []) time := by
  induction k generalizing i with
  | zero => exact ⟨0, by simp, by simp [RunsExactly]⟩
  | succ k ih =>
    let current := (Round.step^[i]) s
    let next := Round.step current
    let w := provider.outputs (current, ([] : List Bool))
    have hc := StateSize.iterate_bits s N i hs (by omega)
    have hn := StateSize.iterate_bits s N (i + 1) hs (by omega)
    have next_eq : next = (Round.step^[i + 1]) s := by
      simp only [next, current, Function.iterate_succ_apply']
    have hp : w.steps ≤ provider.time.eval (2 * StateSize.widthPolynomial.eval N + 1) := by
      apply w.steps_le_m.trans
      apply natPolynomial_eval_mono
      simp only [pairEncoding_length, Frame.wordEncoding, id_eq, List.length_nil, current]
      omega
    have first := BitmapIterate.round_exact provider.machine
      (Round.encoding.encode current) (List.replicate k true) [] [] (Round.encoding.encode next)
      w.steps (by simpa [pairEncoding, Frame.wordEncoding, next, Function.flip_def] using w.evals_in_steps)
    obtain ⟨t, ht, rest⟩ := ih (i + 1) (by omega)
    have firstBound : w.steps + 5 * (Round.encoding.encode current).length +
        2 * (Round.encoding.encode next).length + 11 ≤ roundPolynomial.eval N := by
      rw [next_eq]
      simp only [roundPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
        Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, current]
      omega
    refine ⟨t + (w.steps + 5 * (Round.encoding.encode current).length +
      2 * (Round.encoding.encode next).length + 11), ?_, ?_⟩
    · nlinarith
    · rw [← next_eq] at rest
      have hi : i + 1 + k = i + (k + 1) := by omega
      simpa only [machine, List.length_nil, Nat.mul_zero, Nat.add_zero,
        List.replicate_succ, hi, current, BitmapIterate.machine, Machine.computer, FinTM2.step] using first.trans rest

theorem whole_run (s : Round.State) :
    ∃ time, time ≤ timePolynomial.eval (inputEncoding.encode s).length ∧
      RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode s))
        (haltList machine.computer (Round.encoding.encode (value s))) time := by
  let L := (Round.encoding.encode s).length
  let N := (inputEncoding.encode s).length
  have hN : N = 2 * L + 1 := by simp [N, L, inputEncoding]
  have hcount : s.1 ≤ L := by
    simp only [L, Round.encoding, pairEncoding_length, UnaryBinary.unaryEncoding, List.length_replicate]
    omega
  have hpadded := Round.padded s L hcount
  have prep := BitmapIterate.prepare provider.machine (Round.encoding.encode s) []
  obtain ⟨t, ht, loop⟩ := loop_run s N (by omega) L 0 (by omega)
  have last := BitmapIterate.finish provider.machine
    (Round.encoding.encode ((Round.step^[L]) s)) [] []
  have hout := StateSize.iterate_bits s N L (by omega) (by omega)
  have all := (prep.trans (by simpa [L, machine, BitmapIterate.machine, Machine.computer, FinTM2.step] using loop)).trans last
  refine ⟨(2 * (Round.encoding.encode ((Round.step^[L]) s)).length + 5) +
    (t + (5 * L + 8)), ?_, ?_⟩
  · change _ ≤ timePolynomial.eval N
    have hmul := Nat.mul_le_mul_right (roundPolynomial.eval N) (show L ≤ N by omega)
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  · unfold machine
    rw [BitmapIterate.initial]
    simpa only [machine, inputEncoding, value, hpadded, List.length_nil, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, List.append_nil, L, FinTM2.step] using all

noncomputable def computes : Computes inputEncoding Round.encoding value where
  machine := machine
  time := timePolynomial
  outputs s := {
    steps := Classical.choose (whole_run s)
    evals_in_steps := (Classical.choose_spec (whole_run s)).2
    steps_le_m := (Classical.choose_spec (whole_run s)).1 }

/-- Framing is also a real program, so this accepts the ordinary state codec. -/
noncomputable def fromState : Computes Round.encoding Round.encoding value :=
  (recode (ed := inputEncoding) (g := id) ((encodeComputes Round.encoding).andThen frameComputes)
    id (fun _ => rfl) (fun _ => rfl)).andThen computes

theorem primitive_bound (s : Round.State) :
    primitiveCost fromState.machine (fromState.outputs s).steps
      (some (initList fromState.machine.computer (Round.encoding.encode s))) ≤
      (primitivePolynomial fromState).eval (Round.encoding.encode s).length :=
  computes_primitive_cost fromState s

end Holant.LocalDrafts.Tractability.ProductMachine.Loop
