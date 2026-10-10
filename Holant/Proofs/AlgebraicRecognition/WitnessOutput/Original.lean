import Holant.Proofs.AlgebraicRecognition.WitnessOutput.Search
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.Resources
import Holant.Proofs.Algorithms.TransformRecognition.OriginalSystemWitness


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
open Holant Holant.Tractable Turing Computability
open Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition

def ofOriginal {d k : ℕ} (o : OriginalSystemWitness.Result d k) : Output :=
  ofStructured o.witness o.variables

def originalOutput {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (S : List (Sparse.Poly (5+k) 1))
    (address : Fin m → Fin (5+k)) : Option Output :=
  (OriginalSystemWitness.candidate input hv S address).map ofCandidate

/-- This serialization retains the complete current MainChain result, rather
than producing a second witness after deciding existence. -/
theorem originalOutput_serializes {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (S : List (Sparse.Poly (5+k) 1))
    (address : Fin m → Fin (5+k)) :
    originalOutput input hv S address =
      (OriginalSystemWitness.output input hv S address).map (fun o => ofOriginal o.2) := by
  simp only [originalOutput, OriginalSystemWitness.output, Option.map_map] <;> rfl

theorem originalOutput_eq {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (S : List (Sparse.Poly (5+k) 1))
    (address : Fin m → Fin (5+k)) :
    originalOutput input hv S address =
      sourceOutput (RationalInputSystem.target input S)
        (OriginalSystemDecision.oneSlot S) (OriginalSystemDecision.negSlot S)
        (RationalInputSystem.system S address) (OriginalSystemDecision.target_valid input hv S) := rfl

theorem originalOutput_isSome {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (S : List (Sparse.Poly (5+k) 1))
    (address : Fin m → Fin (5+k)) :
    (originalOutput input hv S address).isSome = true ↔
      OriginalSystemDecision.answer input hv S address = true := by
  simpa only [originalOutput, Option.isSome_map] using
    OriginalSystemWitness.candidate_isSome input hv S address

theorem originalOutput_correct {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (w : Fin m → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ))
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k))
    (hg : SparseTransform.guard RationalCompiler.data k ∈ S) :
    (originalOutput input hv S address).isSome = true ↔
      ∃ z : Fin (5+k) → ℂ, ∀ e ∈ RationalInputSystem.system S address,
        MvPolynomial.aeval z
          (EncodedSystem.polynomial (RationalInputSystem.values (fun i => (w i : ℂ)) S) e) = 0 :=
  (originalOutput_isSome input hv S address).trans
    (OriginalSystemDecision.answer_correct input hv w hw S address hg)

noncomputable section

def originalMachine : Machine := RationalInputMachine.Compiler.executes.machine.compose machine

/-- One fixed physical program from the existing faithful rational-input word
to the exact MainChain witness bytes. Only original descriptor validity is a
semantic input-domain restriction; no accepted witness or stop index is input. -/
theorem original_outputs {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (S : List (Sparse.Poly (5+k) 1))
    (address : Fin m → Fin (5+k)) :
    ∃ ticks, Nonempty (TM2OutputsInTime originalMachine.computer
      (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address))
      (some (resultEncoding.encode (originalOutput input hv S address))) ticks) := by
  obtain ⟨ticks, ⟨searchRun⟩⟩ := outputs (RationalInputSystem.target input S)
    (OriginalSystemDecision.oneSlot S) (OriginalSystemDecision.negSlot S)
    (RationalInputSystem.system S address) (OriginalSystemDecision.target_valid input hv S)
  let frontend := RationalInputMachine.source_outputs input S address
  let full := Machine.compose_correct _ _ _ _ _ _ _ frontend searchRun
  refine ⟨RationalInputMachine.transitions (RationalInputMachine.fromSource input S address) +
    2 * ((NegativeCatalogueMachine.encoding.encode
      (NegativeCatalogueMachine.fromSource (RationalInputSystem.target input S)
        (EncodedGuard.augment (RationalInputMachine.oneSlot S) (RationalInputMachine.negSlot S)
          (RationalInputSystem.system S address)) 0)).length + 1) + ticks, ⟨?_⟩⟩
  simpa only [originalMachine, originalOutput_eq] using full

end

/-- Correctness refers to every original input binding and original rational
equation at the literal returned coordinate values. Output equality gives all
matrix/inverse/scalar bytes; no unrelated algebraic point is selected. -/
theorem original_returned_sound {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (w : Fin m → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ))
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k))
    (o : Output) (ho : originalOutput input hv S address = some o) :
    ∃ a : PositiveWitnessSearch.Candidate (m+RationalInputSystem.count S) k,
      OriginalSystemWitness.candidate input hv S address = some a ∧ o = ofCandidate a ∧
      ∃ θ : AlgebraicComplex, o.root.Represents (θ : ℂ) ∧
        θ^(a.1.1+1) = PowerArithmetic.decode θ a.1.2.1 ∧
        (Kernel.mul
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.matrixCode a.1.2.2.2.2 u v))
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.inverseCode a.1.2.1 a.1.2.2.2.2 u v)) =
            Signature.equality ∧
         Kernel.mul
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.inverseCode a.1.2.1 a.1.2.2.2.2 u v))
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.matrixCode a.1.2.2.2.2 u v)) =
            Signature.equality) ∧
        (∀ i, (PowerArithmetic.decode θ (a.1.2.2.2.2 (address i)) : ℂ) = (w i : ℂ)) ∧
        ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
          (fun i => (PowerArithmetic.decode θ (a.1.2.2.2.2 i) : ℂ)) p = 0 := by
  change (OriginalSystemWitness.candidate input hv S address).map ofCandidate = some o at ho
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.mp ho
  subst o
  obtain ⟨θ, hr, hrel, hinv, hbind, heq⟩ :=
    OriginalSystemWitness.emitted_candidate_sound input hv w hw S address a ha
  exact ⟨a, ha, rfl, θ, hr, hrel, hinv, hbind, heq⟩

/-- Primitive and tape bounds for the same actual composed run. The bound is
obtained from the proven run, not required as a caller-supplied cost premise. -/
theorem original_resources {m k : ℕ} (input : Fin m → RootCode)
    (hv : OriginalSystemDecision.Valid input) (S : List (Sparse.Poly (5+k) 1))
    (address : Fin m → Fin (5+k)) :
    ∃ ticks, ∃ execution : TM2OutputsInTime originalMachine.computer
      (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address))
      (some (resultEncoding.encode (originalOutput input hv S address))) ticks,
      primitiveCost originalMachine execution.steps
        (some (initList originalMachine.computer
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address)))) ≤
          ticks * originalMachine.primitiveBudget ∧
      ∀ i ≤ execution.steps, ∀ c : originalMachine.Config,
        (fun s => s.bind originalMachine.computer.step)^[i]
          (some (initList originalMachine.computer
            (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address)))) = some c →
        stackSize c.stk ≤
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address)).length +
            ticks * originalMachine.primitiveBudget := by
  obtain ⟨ticks, ⟨execution⟩⟩ := original_outputs input hv S address
  refine ⟨ticks, execution, ?_, ?_⟩
  · exact (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ execution.steps_le_m)
  · intro i hi c hc
    have h := originalMachine.run_size_le _ c i hc
    rw [Machine.size_init] at h
    exact h.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (hi.trans execution.steps_le_m)) _)

end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
