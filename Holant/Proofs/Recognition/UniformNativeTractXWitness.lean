import Holant.Proofs.Recognition.UniformNativeTractXSemantics
import Holant.Proofs.Recognition.UniformTractXWitness
import Holant.Proofs.Recognition.PhysicalFolds

/-!
# Physical native A/P/L witness packets from original coefficient descriptors

A fixed physical recoder sets the mandatory edge to disequality before the raw
system preparation. It neither transforms nor re-isolates any source coefficient.
The returned packet is the actual candidate serialized by the witness search,
with all original coefficients, native edge values and literal equations retained.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformNativeTractXWitness
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open PhysicalFolds UniformTensorDecisionBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Kind := UniformTractXWitness.Kind
variable {s : ℕ} (arity : Fin s → ℕ)
abbrev Entries := UniformTractXWitness.Entries arity
abbrev body := UniformTractXWitness.body arity
abbrev address := UniformTractXWitness.address arity

def nativeEdge (r : OriginalFamilyPackingMachine.Input) : OriginalFamilyPackingMachine.Input := (r.1,true)
def nativeEdgeComputes : Computes OriginalFamilyPackingMachine.encoding
    OriginalFamilyPackingMachine.encoding nativeEdge :=
  pairComputes OriginalFamilyPackingMachine.family
    (constantComputes OriginalFamilyPackingMachine.encoding encodingBoolBool true)

abbrev nativeOriginal (d : Data s arity) := OriginalFamilyPackingSource.fromSource arity d.input true
abbrev descriptors (input : OriginalFamilyInput.Input arity) :=
  OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input true)
def values (d : Data s arity) : Fin (Entries arity+2) → AlgebraicComplex :=
  OriginalAffineDecision.originalValues arity (OriginalFamilyInput.values arity d.G true)

theorem descriptors_represents (d : Data s arity) : ∀ i,
    (descriptors arity d.input i).Represents (values arity d i : ℂ) := by
  intro i
  rw [values,congrFun (OriginalAffineDecision.originalValues_coe arity
    (OriginalFamilyInput.values arity d.G true)) i]
  exact OriginalVariableLayout.descriptors_represents _ _
    (OriginalFamilyInput.pack_represents arity d.input d.G d.represented true) i

theorem descriptorValid (d : Data s arity) : OriginalSystemDecision.Valid (descriptors arity d.input) :=
  ⟨values arity d,descriptors_represents arity d⟩

def output (kind : Kind) (d : Data s arity) : Option WitnessOutput.Output :=
  WitnessOutput.originalOutput (descriptors arity d.input) (descriptorValid arity d)
    (body arity kind d.input) (address arity kind)

theorem request_exact (kind : Kind) (input : OriginalFamilyInput.Input arity) :
    UniformTractXWitness.request kind (OriginalFamilyPackingSource.fromSource arity input true) =
      RationalInputMachine.fromSource (descriptors arity input) (body arity kind input) (address arity kind) := by
  cases kind with
  | affine => exact RawAffineRecognitionSource.request_exact arity input true
  | product => exact RawProductRecognitionSource.request_exact arity input true
  | localAffine => exact RawLocalAffineRecognitionSource.request_exact arity input true

/-- A single class-tagged programme; no chosen successful basis or witness is input. -/
def machine (kind : Kind) : BinaryCompose.Machine :=
  nativeEdgeComputes.machine.compose
    ((UniformTractXWitness.prepare kind).machine.compose WitnessOutput.originalMachine)

theorem outputs (kind : Kind) (d : Data s arity) : ∃ ticks,
    Nonempty (TM2OutputsInTime (machine kind).computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (WitnessOutput.resultEncoding.encode (output arity kind d))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := WitnessOutput.original_outputs
    (descriptors arity d.input) (descriptorValid arity d) (body arity kind d.input) (address arity kind)
  have middle := (UniformTractXWitness.prepare kind).outputs (nativeOriginal arity d)
  rw [nativeOriginal,request_exact] at middle
  have joined := Machine.compose_correct _ _ _ _ _ _ _ middle right
  have left := nativeEdgeComputes.outputs (original arity d)
  change TM2OutputsInTime nativeEdgeComputes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (original arity d))
    (some (OriginalFamilyPackingMachine.encoding.encode (nativeOriginal arity d))) _ at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left joined⟩⟩

def runs (kind : Kind) : Runs OriginalFamilyPackingMachine.encoding WitnessOutput.resultEncoding
    (original arity) (output arity kind) where
  machine := machine kind
  cost d := Classical.choose (outputs arity kind d)
  outputs d := Classical.choice (Classical.choose_spec (outputs arity kind d))

def answer (kind : Kind) (d : Data s arity) : Bool :=
  match kind with
  | .affine => UniformNativeTractXSemantics.affine arity d
  | .product => UniformNativeTractXSemantics.product arity d
  | .localAffine => UniformNativeTractXSemantics.localAffine arity d

theorem output_isSome (kind : Kind) (d : Data s arity) :
    (output arity kind d).isSome=true ↔ answer arity kind d=true := by
  rw [output,WitnessOutput.originalOutput_isSome]
  cases kind <;> rfl

theorem output_correct (kind : Kind) (d : Data s arity) :
    (output arity kind d).isSome=true ↔
      CommonTransformable (UniformTractXWitness.target kind) (UniformNativeTractXSemantics.family arity d) := by
  rw [output_isSome]
  cases kind with
  | affine => exact UniformNativeTractXSemantics.affine_correct arity d
  | product => exact UniformNativeTractXSemantics.product_correct arity d
  | localAffine => exact UniformNativeTractXSemantics.localAffine_correct arity d

theorem none_iff (kind : Kind) (d : Data s arity) :
    output arity kind d=none ↔
      ¬CommonTransformable (UniformTractXWitness.target kind) (UniformNativeTractXSemantics.family arity d) := by
  rw [←output_correct arity kind d]
  cases output arity kind d <;> simp

/-- The serialized coordinates belong to the actual returned search candidate,
not a separately selected semantic witness. The bindings include native X. -/
theorem returned_sound (kind : Kind) (d : Data s arity) (o : WitnessOutput.Output)
    (ho : output arity kind d=some o) :
    ∃ c : OriginalSystemWitness.Candidate (m:=Entries arity+2) (body arity kind d.input),
      OriginalSystemWitness.candidate (descriptors arity d.input) (descriptorValid arity d)
        (body arity kind d.input) (address arity kind)=some c ∧
      o=WitnessOutput.ofCandidate c ∧ ∃ θ : AlgebraicComplex, o.root.Represents (θ : ℂ) ∧
      (∀ i, (PowerArithmetic.decode θ (c.1.2.2.2.2 (address arity kind i)) : ℂ)=
        (values arity d i : ℂ)) ∧
      ∀ p ∈ body arity kind d.input,
        SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
          (fun i => (PowerArithmetic.decode θ (c.1.2.2.2.2 i) : ℂ)) p=0 := by
  obtain ⟨c,hc,ho,θ,hθ,_,_,hb,he⟩ := WitnessOutput.original_returned_sound
    (descriptors arity d.input) (descriptorValid arity d) (values arity d)
    (descriptors_represents arity d) (body arity kind d.input) (address arity kind) o ho
  exact ⟨c,hc,ho,θ,hθ,hb,he⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformNativeTractXWitness
