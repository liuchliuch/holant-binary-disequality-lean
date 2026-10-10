import Holant.Proofs.Counting.RawGraphMachine.Bounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateFinish


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine.Loop
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol

def encoding : Encoding Work Bool where
  encode s := frame (workEncoding.encode s)
  decode bits := do
    let (word, rest) ← unframe bits
    if rest = [] then workEncoding.decode word else none
  decode_encode s := by
    have h : unframe (frame (workEncoding.encode s)) = some (workEncoding.encode s,[]) := by
      simpa only [List.append_nil] using unframe_frame_append (workEncoding.encode s) []
    simp [h]

def provider : Computes (pairEncoding workEncoding Frame.wordEncoding) workEncoding
    (fun p => advance p.1) :=
  (Wiring.firstComputes workEncoding Frame.wordEncoding).andThen Stages.advanceComputes

abbrev machine := BitmapIterate.machine provider.machine
def value (s : Work) := (advance^[Bounds.width s]) s

def roundPolynomial : Polynomial ℕ :=
  provider.time.comp (2 * Bounds.storagePolynomial + 1) + 7 * Bounds.storagePolynomial + 11
def timePolynomial : Polynomial ℕ :=
  Polynomial.X * roundPolynomial + 7 * Bounds.storagePolynomial + 13

theorem round_run (s : Work) (j : ℕ) (hj : j + 1 ≤ Bounds.width s) (index : List Bool) :
    ∃ ticks, ticks ≤ roundPolynomial.eval (Bounds.width s) ∧
      RunsExactly machine.computer.step
        (BitmapIterate.ready provider.machine (BitmapIterate.phase provider.machine 5)
          (workEncoding.encode ((advance^[j]) s)) [] (true :: index) [] [] [])
        (BitmapIterate.ready provider.machine (BitmapIterate.phase provider.machine 5)
          (workEncoding.encode ((advance^[j + 1]) s)) [] index [] [] []) ticks := by
  let current := (advance^[j]) s
  let o := provider.outputs (current, ([] : List Bool))
  have first := BitmapIterate.round_exact provider.machine (workEncoding.encode current)
    index [] [] (workEncoding.encode (advance current)) o.steps
    (by simpa [pairEncoding, Frame.wordEncoding, Function.flip_def] using o.evals_in_steps)
  have h₀ := Bounds.iterate_width s j (by omega)
  have h₁ := Bounds.iterate_width s (j + 1) hj
  have ho : o.steps ≤ provider.time.eval (2 * Bounds.storagePolynomial.eval (Bounds.width s) + 1) := by
    apply o.steps_le_m.trans
    apply natPolynomial_eval_mono
    simpa [pairEncoding_length, Frame.wordEncoding, Bounds.width, current] using
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 h₀) 1
  refine ⟨o.steps + 5 * Bounds.width current + 2 * Bounds.width (advance current) + 11, ?_, ?_⟩
  · have h₁' : Bounds.width (advance current) ≤ Bounds.storagePolynomial.eval (Bounds.width s) := by
      simpa [current, Function.iterate_succ_apply'] using h₁
    change Bounds.width current ≤ _ at h₀
    simp only [roundPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
    omega
  · simpa only [machine, List.length_nil, Nat.mul_zero, Nat.add_zero, Bounds.width,
      current, Function.iterate_succ_apply', FinTM2.step] using first

/-- Precise controller invariant: current word is advance^j of the initial
word, remaining unary counter has k tokens, j+k is within the scanned width,
and all provider/snapshot scratch stacks are empty at the call boundary. -/
theorem rounds_run (s : Work) (k j : ℕ) (hk : j + k ≤ Bounds.width s) :
    ∃ ticks, ticks ≤ k * roundPolynomial.eval (Bounds.width s) ∧
      RunsExactly machine.computer.step
        (BitmapIterate.ready provider.machine (BitmapIterate.phase provider.machine 5)
          (workEncoding.encode ((advance^[j]) s)) [] (List.replicate k true) [] [] [])
        (BitmapIterate.ready provider.machine (BitmapIterate.phase provider.machine 5)
          (workEncoding.encode ((advance^[j + k]) s)) [] [] [] [] []) ticks := by
  induction k generalizing j with
  | zero => exact ⟨0, by simp, by simp [RunsExactly]⟩
  | succ k ih =>
    obtain ⟨a, ha, first⟩ := round_run s j (by omega) (List.replicate k true)
    obtain ⟨b, hb, rest⟩ := ih (j + 1) (by omega)
    refine ⟨b + a, ?_, ?_⟩
    · rw [Nat.succ_mul]; omega
    · simpa only [List.replicate_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using first.trans rest

theorem whole_run (s : Work) :
    ∃ ticks, ticks ≤ timePolynomial.eval (encoding.encode s).length ∧
      RunsExactly machine.computer.step
        (initList machine.computer (encoding.encode s))
        (haltList machine.computer (workEncoding.encode (value s))) ticks := by
  have prep := BitmapIterate.prepare provider.machine (workEncoding.encode s) []
  obtain ⟨t, ht, run⟩ := rounds_run s (Bounds.width s) 0 (by omega)
  have last := BitmapIterate.finish provider.machine (workEncoding.encode (value s)) [] []
  simp only [Nat.zero_add, Function.iterate_zero, id_eq] at run
  have all := (prep.trans run).trans last
  have hb := Bounds.iterate_width s (Bounds.width s) le_rfl
  have hbase := Bounds.width_le_storage (Bounds.width s)
  have hn : Bounds.width s ≤ (encoding.encode s).length := by
    simp only [Bounds.width, encoding, frame_length]
    omega
  have hmono : timePolynomial.eval (Bounds.width s) ≤ timePolynomial.eval (encoding.encode s).length :=
    natPolynomial_eval_mono timePolynomial hn
  refine ⟨(2 * Bounds.width (value s) + 5) + (t + (5 * Bounds.width s + 8)), ?_, ?_⟩
  · apply le_trans ?_ hmono
    change Bounds.width (value s) ≤ _ at hb
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  · rw [BitmapIterate.initial]
    simpa only [machine, encoding, value, Bounds.width, List.length_nil, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, List.append_nil, FinTM2.step] using all

def computes : Computes encoding workEncoding value where
  machine := machine
  time := timePolynomial
  outputs s := by
    let t := Classical.choose (whole_run s)
    have ht := Classical.choose_spec (whole_run s)
    exact { steps := t, evals_in_steps := ht.2, steps_le_m := ht.1 }

/-- This input frame is physically emitted, not inserted by changing codecs. -/
def frameComputes : Computes workEncoding encoding id :=
  recode ((FixedGadgetSubstitution.Compiler.encodeComputes workEncoding).andThen
    FixedGadgetSubstitution.Compiler.frameComputes) id (fun _ => rfl) (fun _ => rfl)

end Holant.LocalDrafts.CountingHardness.RawGraphMachine.Loop
