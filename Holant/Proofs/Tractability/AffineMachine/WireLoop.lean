import Holant.Proofs.Tractability.AffineMachine.WireSize
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateFinish


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.WireLoop

open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol FixedGadgetSubstitution.Compiler

variable {s b : ℕ}

noncomputable def inputEncoding : Encoding (WireRound.State (s := s) (b := b)) Bool where
  encode x := frame (WireRound.encoding.encode x)
  decode bits := do
    let (word, rest) ← unframe bits
    if rest = [] then WireRound.encoding.decode word else none
  decode_encode x := by
    have hf : unframe (frame (WireRound.encoding.encode x)) = some (WireRound.encoding.encode x, []) := by
      simpa only [List.append_nil] using unframe_frame_append (WireRound.encoding.encode x) []
    rw [hf]
    simp


noncomputable def provider :
    Computes (pairEncoding (WireRound.encoding (s := s) (b := b)) Frame.wordEncoding)
      WireRound.encoding (fun x => WireRound.step x.1) :=
  (Wiring.firstComputes WireRound.encoding Frame.wordEncoding).andThen WireRound.computes

noncomputable def machine := BitmapIterate.machine (provider (s := s) (b := b)).machine

noncomputable def roundPolynomial (s b : ℕ) : Polynomial ℕ :=
  (provider (s := s) (b := b)).time.comp (2 * WireSize.widthPolynomial s b + 1) +
    7 * WireSize.widthPolynomial s b + 11

noncomputable def timePolynomial (s b : ℕ) : Polynomial ℕ :=
  5 * Polynomial.X + 8 + Polynomial.X * roundPolynomial s b +
    2 * WireSize.widthPolynomial s b + 5

def value (x : WireRound.State (s := s) (b := b)) := (WireRound.step^[x.1.1]) x

theorem loop_run (x : WireRound.State (s := s) (b := b)) (N : ℕ)
    (hx : (WireRound.encoding.encode x).length ≤ N) (k i : ℕ) (hki : i + k ≤ N) :
    ∃ time, time ≤ k * (roundPolynomial s b).eval N ∧
      RunsExactly (machine (s := s) (b := b)).computer.step
        (BitmapIterate.ready (provider (s := s) (b := b)).machine (BitmapIterate.phase (provider (s := s) (b := b)).machine 5)
          (WireRound.encoding.encode ((WireRound.step^[i]) x)) [] (List.replicate k true) [] [] [])
        (BitmapIterate.ready (provider (s := s) (b := b)).machine (BitmapIterate.phase (provider (s := s) (b := b)).machine 5)
          (WireRound.encoding.encode ((WireRound.step^[i + k]) x)) [] [] [] [] []) time := by
  induction k generalizing i with
  | zero => exact ⟨0, by simp, by simp [RunsExactly]⟩
  | succ k ih =>
    let current := (WireRound.step^[i]) x
    let next := WireRound.step current
    let w := (provider (s := s) (b := b)).outputs (current, ([] : List Bool))
    have hc := WireSize.iterate_bits x N i hx (by omega)
    have hn := WireSize.iterate_bits x N (i + 1) hx (by omega)
    have next_eq : next = (WireRound.step^[i + 1]) x := by
      simp only [next, current, Function.iterate_succ_apply']
    have hp : w.steps ≤ (provider (s := s) (b := b)).time.eval (2 * (WireSize.widthPolynomial s b).eval N + 1) := by
      apply w.steps_le_m.trans
      apply natPolynomial_eval_mono
      simp only [pairEncoding_length, Frame.wordEncoding, id_eq, List.length_nil, current]
      omega
    have first := BitmapIterate.round_exact (provider (s := s) (b := b)).machine
      (WireRound.encoding.encode current) (List.replicate k true) [] []
      (WireRound.encoding.encode next) w.steps
      (by simpa [pairEncoding, Frame.wordEncoding, next, Function.flip_def] using w.evals_in_steps)
    obtain ⟨t, ht, rest⟩ := ih (i + 1) (by omega)
    have firstBound : w.steps + 5 * (WireRound.encoding.encode current).length +
        2 * (WireRound.encoding.encode next).length + 11 ≤ (roundPolynomial s b).eval N := by
      rw [next_eq]
      simp only [roundPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
        Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, current]
      omega
    refine ⟨t + (w.steps + 5 * (WireRound.encoding.encode current).length +
      2 * (WireRound.encoding.encode next).length + 11), ?_, ?_⟩
    · nlinarith
    · rw [← next_eq] at rest
      have hi : i + 1 + k = i + (k + 1) := by omega
      simpa only [machine, List.length_nil, Nat.mul_zero, Nat.add_zero,
        List.replicate_succ, hi, current, BitmapIterate.machine, Machine.computer, FinTM2.step] using first.trans rest

theorem whole_run (x : WireRound.State (s := s) (b := b)) :
    ∃ time, time ≤ (timePolynomial s b).eval (inputEncoding.encode x).length ∧
      RunsExactly (machine (s := s) (b := b)).computer.step (initList (machine (s := s) (b := b)).computer (inputEncoding.encode x))
        (haltList (machine (s := s) (b := b)).computer (WireRound.encoding.encode (value x))) time := by
  let L := (WireRound.encoding.encode x).length
  let N := (inputEncoding.encode x).length
  have hN : N = 2 * L + 1 := by simp [N, L, inputEncoding]
  have hcount : x.1.1 ≤ L := (WireSize.initial_parts x L le_rfl).1
  have hpadded := WireRound.padded x L hcount
  have prep := BitmapIterate.prepare (provider (s := s) (b := b)).machine (WireRound.encoding.encode x) []
  obtain ⟨t, ht, loop⟩ := loop_run x N (by omega) L 0 (by omega)
  have last := BitmapIterate.finish (provider (s := s) (b := b)).machine
    (WireRound.encoding.encode ((WireRound.step^[L]) x)) [] []
  have hout := WireSize.iterate_bits x N L (by omega) (by omega)
  have all := (prep.trans (by simpa [L, machine, BitmapIterate.machine, Machine.computer, FinTM2.step] using loop)).trans last
  refine ⟨(2 * (WireRound.encoding.encode ((WireRound.step^[L]) x)).length + 5) +
    (t + (5 * L + 8)), ?_, ?_⟩
  · change _ ≤ (timePolynomial s b).eval N
    have hmul := Nat.mul_le_mul_right ((roundPolynomial s b).eval N) (show L ≤ N by omega)
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  · unfold machine
    rw [BitmapIterate.initial]
    simpa only [machine, inputEncoding, value, hpadded, List.length_nil, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, List.append_nil, L, FinTM2.step] using all

noncomputable def computes : Computes (inputEncoding (s := s) (b := b)) WireRound.encoding value where
  machine := machine
  time := timePolynomial s b
  outputs x := {
    steps := Classical.choose (whole_run x)
    evals_in_steps := (Classical.choose_spec (whole_run x)).2
    steps_le_m := (Classical.choose_spec (whole_run x)).1 }

noncomputable def fromState : Computes (WireRound.encoding (s := s) (b := b)) WireRound.encoding value :=
  (recode (ed := inputEncoding) (g := id) ((encodeComputes WireRound.encoding).andThen frameComputes)
    id (fun _ => rfl) (fun _ => rfl)).andThen computes

theorem terminal (x : WireRound.State (s := s) (b := b)) : (value x).1.1 = 0 := by
  have h := WireRound.dimension_iterate x x.1.1
  simpa [value] using h

theorem primitive_bound (x : WireRound.State (s := s) (b := b)) :
    primitiveCost fromState.machine (fromState.outputs x).steps
      (some (initList (fromState (s := s) (b := b)).machine.computer (WireRound.encoding.encode x))) ≤
        (primitivePolynomial (fromState (s := s) (b := b))).eval (WireRound.encoding.encode x).length :=
  computes_primitive_cost fromState x

end Holant.LocalDrafts.Tractability.AffineMachine.WireLoop
