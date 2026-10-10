import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Controller
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionUniqueness


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Source
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open GraphPreprocessing.OriginalCoefficient.ResidualExpansion (machine_output_unique)
open ComplexIsolation.CertificateMachine (rootEncoding)

noncomputable section

abbrev generation := Enumeration.executes
abbrev stageProgram := stageExecutes
abbrev machine := Controller.machine
abbrev inputEncoding := contextEncoding
abbrev bound := Controller.totalBound
abbrev outputs := Controller.total
abbrev outputs_correct := Controller.total_correct
abbrev source_outputs := Controller.source_outputs
abbrev primitives := Controller.primitives
abbrev prefix_bits := Controller.prefix_bits

/-- Soundness of ANY actual Bool output, not only of the exhibited terminating
run. Determinism and faithful Bool bytes identify it with the proved output. -/
theorem output_correct (x : Context) (z : ℂ) (hz : x.1.Represents z) (b : Bool) (ticks : ℕ)
    (out : TM2OutputsInTime machine.computer (inputEncoding.encode x)
      (some (encodingBoolBool.encode b)) ticks) :
    b=true ↔ Polynomial.aeval z x.2.polynomial=0 := by
  obtain ⟨n,d,⟨known⟩,hd⟩ := outputs_correct x z hz
  have hw := machine_output_unique machine _ _ _ out.steps known.steps
    out.evals_in_steps known.evals_in_steps
  have hb : b=d := encodingBoolBool.encode_injective hw
  rw [hb]
  exact hd

theorem output_false_iff (x : Context) (z : ℂ) (hz : x.1.Represents z) (b : Bool) (ticks : ℕ)
    (out : TM2OutputsInTime machine.computer (inputEncoding.encode x)
      (some (encodingBoolBool.encode b)) ticks) :
    b=false ↔ Polynomial.aeval z x.2.polynomial≠0 := by
  have h := output_correct x z hz b ticks out
  cases b <;> simpa using not_congr h

theorem same_context_bytes (r : Request) (n : ℕ) :
    contextEncoding.encode (Controller.advance r n).1=contextEncoding.encode r.1 := by
  rw [Controller.advance_context]

abbrev ListInput := RootCode × List ℚ
abbrev listInputEncoding := pairEncoding rootEncoding CommonFieldMachine.coordinatesEncoding
def listContext (x : ListInput) : Context := (x.1,Code.dense x.2)

def listPrepare : Computes listInputEncoding contextEncoding listContext :=
  pairComputes (Wiring.firstComputes rootEncoding CommonFieldMachine.coordinatesEncoding)
    ((Wiring.secondComputes rootEncoding CommonFieldMachine.coordinatesEncoding).andThen CodePrograms.denseComputes)

/-- The dense adapter preserves the original RootCode bytes and the original
coordinate entries; the already physical dense program produces sparse q. -/
def listMachine := listPrepare.machine.compose machine
def listBound (n : ℕ) (x : ListInput) (b : Bool) : ℕ :=
  listPrepare.time.eval (listInputEncoding.encode x).length+
    2*((contextEncoding.encode (listContext x)).length+1)+bound n (listContext x) b

theorem list_source_outputs (x : ListInput) (hv : Valid x.1) :
    ∃ n, Nonempty (TM2OutputsInTime listMachine.computer (listInputEncoding.encode x)
      (some (encodingBoolBool.encode (zeroList x.1 x.2 hv)))
      (listBound n x (zeroList x.1 x.2 hv))) := by
  obtain ⟨n,⟨known⟩⟩ := source_outputs (listContext x) hv
  exact ⟨n,⟨Machine.compose_correct _ _ _ _ _ _ _ (listPrepare.outputs x) known⟩⟩

theorem list_outputs_correct (x : ListInput) (z : ℂ) (hz : x.1.Represents z) :
    ∃ n b, Nonempty (TM2OutputsInTime listMachine.computer (listInputEncoding.encode x)
      (some (encodingBoolBool.encode b)) (listBound n x b)) ∧
      (b=true ↔ BranchConsumers.decodeList z x.2=0) := by
  obtain ⟨n,b,⟨known⟩,hb⟩ := outputs_correct (listContext x) z hz
  refine ⟨n,b,⟨Machine.compose_correct _ _ _ _ _ _ _ (listPrepare.outputs x) known⟩,?_⟩
  simpa only [listContext,Code.dense_correct] using hb

theorem list_output_correct (x : ListInput) (z : ℂ) (hz : x.1.Represents z)
    (b : Bool) (ticks : ℕ) (out : TM2OutputsInTime listMachine.computer (listInputEncoding.encode x)
      (some (encodingBoolBool.encode b)) ticks) :
    b=true ↔ BranchConsumers.decodeList z x.2=0 := by
  obtain ⟨n,d,⟨known⟩,hd⟩ := list_outputs_correct x z hz
  have hw := machine_output_unique listMachine _ _ _ out.steps known.steps
    out.evals_in_steps known.evals_in_steps
  have hb : b=d := encodingBoolBool.encode_injective hw
  rw [hb]
  exact hd

theorem list_output_false_iff (x : ListInput) (z : ℂ) (hz : x.1.Represents z)
    (b : Bool) (ticks : ℕ) (out : TM2OutputsInTime listMachine.computer (listInputEncoding.encode x)
      (some (encodingBoolBool.encode b)) ticks) :
    b=false ↔ BranchConsumers.decodeList z x.2≠0 := by
  have h := list_output_correct x z hz b ticks out
  cases b <;> simpa using not_congr h

theorem list_primitives (n : ℕ) (x : ListInput) (b : Bool)
    (out : TM2OutputsInTime listMachine.computer (listInputEncoding.encode x)
      (some (encodingBoolBool.encode b)) (listBound n x b)) :
    primitiveCost listMachine out.steps (some (initList listMachine.computer (listInputEncoding.encode x))) ≤
      listBound n x b*listMachine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ out.steps_le_m)

theorem list_prefix_bits (n : ℕ) (x : ListInput) (b : Bool)
    (out : TM2OutputsInTime listMachine.computer (listInputEncoding.encode x)
      (some (encodingBoolBool.encode b)) (listBound n x b))
    (j : ℕ) (hj : j ≤ out.steps) (c : listMachine.Config)
    (hc : (fun p => p.bind listMachine.computer.step)^[j]
      (some (initList listMachine.computer (listInputEncoding.encode x)))=some c) :
    stackSize c.stk ≤ (listInputEncoding.encode x).length+listBound n x b*listMachine.primitiveBudget := by
  have hs := listMachine.run_size_le (initList listMachine.computer (listInputEncoding.encode x)) c j hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hj.trans out.steps_le_m)) _)

/-- Actual terminating physical output for the required X²-X isolating-zero
counterexample. The nonzero coordinate [0,1] is not replaced by an all-zero
list, and the original reducible relation is not replaced by X. -/
theorem splitRoot_physical_zero :
    ∃ n, Nonempty (TM2OutputsInTime listMachine.computer
      (listInputEncoding.encode (BranchConsumers.splitRoot,[0,1]))
      (some (encodingBoolBool.encode true))
      (listBound n (BranchConsumers.splitRoot,[0,1]) true)) := by
  obtain ⟨n,b,hout,hb⟩ := list_outputs_correct (BranchConsumers.splitRoot,[0,1])
    0 BranchConsumers.splitRoot_represents_zero
  have ht : b=true := hb.mpr BranchConsumers.reducible_relation_boundary.2.2
  exact ⟨n,by simpa only [ht] using hout⟩
end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Source
