import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateFinish
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxPrimitives


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.GrowingLoop
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol
open UniversalPairReduction.SmoothingCompiler

variable {A : Type} {e : Encoding A Bool} {f : A → A}

def inputEncoding (e : Encoding A Bool) : Encoding A Bool where
  encode a := frame (e.encode a)
  decode bits := do
    let (word,rest) ← unframe bits
    if rest = [] then e.decode word else none
  decode_encode a := by
    have hf : unframe (frame (e.encode a)) = some (e.encode a,[]) := by
      simpa only [List.append_nil] using unframe_frame_append (e.encode a) []
    simp [hf,e.decode_encode]

noncomputable def provider (w : Computes e e f) :
    Computes (pairEncoding e Frame.wordEncoding) e (fun p => f p.1) :=
  (Wiring.firstComputes e Frame.wordEncoding).andThen w
noncomputable def machine (w : Computes e e f) := BitmapIterate.machine (provider w).machine

noncomputable def nextWidth (w : Computes e e f) (N : ℕ) : ℕ :=
  (provider w).outputBound.bound.eval (2*N+1)
noncomputable def roundBound (w : Computes e e f) (N : ℕ) : ℕ :=
  (provider w).time.eval (2*N+1) + 5*N + 2*nextWidth w N + 11
noncomputable def loopBound (w : Computes e e f) : ℕ → ℕ → ℕ
  | 0,N => 2*N+5
  | k+1,N => roundBound w N + loopBound w k (nextWidth w N)

theorem next_width (w : Computes e e f) (a : A) (N : ℕ)
    (h : (e.encode a).length ≤ N) : (e.encode (f a)).length ≤ nextWidth w N := by
  have ho := (provider w).outputBound.length_le (a,([] : List Bool))
  apply ho.trans
  unfold nextWidth
  apply natPolynomial_eval_mono
  rw [pairEncoding_length]
  change 2*(e.encode a).length+1+0 ≤ 2*N+1
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Exact calls, table replacement, EOF and final cleanup, with growing tapes. -/
theorem loop_run (w : Computes e e f) (k : ℕ) (a : A) (N : ℕ)
    (ha : (e.encode a).length ≤ N) :
    ∃ ticks, ticks ≤ loopBound w k N ∧
      RunsExactly (machine w).computer.step
        (BitmapIterate.ready (provider w).machine (BitmapIterate.phase (provider w).machine 5)
          (e.encode a) [] (List.replicate k true) [] [] [])
        (haltList (machine w).computer (e.encode ((f^[k]) a))) ticks := by
  induction k generalizing a N with
  | zero =>
    refine ⟨2*(e.encode a).length+5, ?_, ?_⟩
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 5
    · simpa only [machine, Machine.computer, FinTM2.step, BitmapIterate.machine, Function.iterate_zero, id_eq, List.replicate_zero,
        List.length_nil, Nat.zero_add, List.append_nil] using
          BitmapIterate.finish (provider w).machine (e.encode a) [] []
  | succ k ih =>
    let p := provider w
    let o := p.outputs (a,([] : List Bool))
    have first := BitmapIterate.round_exact p.machine (e.encode a)
      (List.replicate k true) [] [] (e.encode (f a)) o.steps
      (by exact o.evals_in_steps)
    have hn := next_width w a N ha
    obtain ⟨t,ht,rest⟩ := ih (f a) (nextWidth w N) hn
    have ho : o.steps ≤ p.time.eval (2*N+1) := by
      apply o.steps_le_m.trans
      apply natPolynomial_eval_mono
      rw [pairEncoding_length]
      change 2*(e.encode a).length+1+0 ≤ 2*N+1
      omega
    have hb : o.steps+5*(e.encode a).length+2*(e.encode (f a)).length+11 ≤
        roundBound w N := by unfold roundBound; dsimp [p] at ho; omega
    refine ⟨t+(o.steps+5*(e.encode a).length+2*(e.encode (f a)).length+11), ?_, ?_⟩
    · simp only [loopBound]; omega
    · simpa only [machine, Machine.computer, FinTM2.step, BitmapIterate.machine, List.length_nil, Nat.mul_zero, Nat.add_zero,
        List.replicate_succ, Function.iterate_succ_apply, Nat.add_assoc, p] using first.trans rest

def value (e : Encoding A Bool) (f : A → A) (a : A) := (f^[(e.encode a).length]) a
noncomputable def bound (w : Computes e e f) (a : A) :=
  5*(e.encode a).length+8+loopBound w (e.encode a).length (e.encode a).length

theorem whole_run (w : Computes e e f) (a : A) :
    ∃ ticks, ticks ≤ bound w a ∧
      RunsExactly (machine w).computer.step
        (initList (machine w).computer ((inputEncoding e).encode a))
        (haltList (machine w).computer (e.encode (value e f a))) ticks := by
  have prep := BitmapIterate.prepare (provider w).machine (e.encode a) []
  obtain ⟨t,ht,run⟩ := loop_run w (e.encode a).length a (e.encode a).length le_rfl
  refine ⟨t+(5*(e.encode a).length+8), by unfold bound; omega, ?_⟩
  unfold machine inputEncoding
  rw [BitmapIterate.initial]
  simpa only [machine, Machine.computer, FinTM2.step, BitmapIterate.machine, inputEncoding, value, List.length_nil, Nat.mul_zero,
    Nat.add_zero, List.append_nil] using prep.trans run

/-- Counts primitive push/pop/load actions, not only provider invocations. -/
theorem whole_primitive (w : Computes e e f) (a : A) :
    ∃ ticks, RunsExactly (machine w).computer.step
        (initList (machine w).computer ((inputEncoding e).encode a))
        (haltList (machine w).computer (e.encode (value e f a))) ticks ∧
      primitiveCost (machine w) ticks
        (some (initList (machine w).computer ((inputEncoding e).encode a))) ≤
          bound w a * (machine w).primitiveBudget := by
  obtain ⟨t,ht,run⟩ := whole_run w a
  exact ⟨t,run,(primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ ht)⟩

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.GrowingLoop
