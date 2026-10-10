import Holant.Proofs.Recognition.UniformTractXSemantics

/-!
# Actual encoded A/P/L witnesses from the same original descriptor word

The existing raw family programs prepare their actual disjunctive polynomial
systems. Composing them with the established witness-producing root search
returns the serialized accepted coordinates, or `none` on a negative answer.
No fresh mathematical basis is substituted for the returned bytes. The soundness
statement retains the returned candidate, its root, every original binding,
and every equation of the actual generated source system.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTractXWitness

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open UniformTensorDecisionBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Kind where
  | affine
  | product
  | localAffine
  deriving DecidableEq

variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Entries := OriginalAffineSystem.Entries arity

def parameters : Kind → ℕ
  | .affine => s+1
  | .product => OriginalProductSystem.Count arity
  | .localAffine => OriginalLocalAffineSystem.Count arity
abbrev Extra (kind : Kind) := OriginalVariableLayout.Extra (Entries arity) (parameters arity kind)

def body (kind : Kind) (input : OriginalFamilyInput.Input arity) :
    List (Sparse.Poly (5+Extra arity kind) 1) :=
  match kind with
  | .affine => RawAffineRecognitionSource.combined arity input
  | .product => RawProductRecognitionSource.combined arity input
  | .localAffine => RawLocalAffineRecognitionSource.combined arity input

def address (kind : Kind) : Fin (Entries arity+2) → Fin (5+Extra arity kind) :=
  OriginalVariableLayout.binding (Entries arity) (parameters arity kind)

abbrev descriptors (input : OriginalFamilyInput.Input arity) :=
  OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input false)

theorem descriptorValid (d : Data s arity) : OriginalSystemDecision.Valid (descriptors arity d.input) :=
  OriginalAffineBranchMachine.descriptors_valid arity _
    (OriginalFamilyInput.pack_valid arity d.input (UniformTractXSemantics.valid arity d) false)

def request : Kind → OriginalFamilyPackingMachine.Input → RationalInputMachine.Input
  | .affine => RawAffineRecognitionMachine.request
  | .product => RawProductRecognitionMachine.request
  | .localAffine => RawLocalAffineRecognitionMachine.request

def prepare (kind : Kind) : CommonFieldMachine.Executes
    OriginalFamilyPackingMachine.encoding RationalInputMachine.encoding (request kind) :=
  match kind with
  | .affine => RawAffineRecognitionMachine.prepare
  | .product => RawProductRecognitionMachine.prepare
  | .localAffine => RawLocalAffineRecognitionMachine.prepare

theorem request_exact (kind : Kind) (input : OriginalFamilyInput.Input arity) :
    request kind (OriginalFamilyPackingSource.fromSource arity input false) =
      RationalInputMachine.fromSource (descriptors arity input) (body arity kind input) (address arity kind) := by
  cases kind with
  | affine => exact RawAffineRecognitionSource.request_exact arity input false
  | product => exact RawProductRecognitionSource.request_exact arity input false
  | localAffine => exact RawLocalAffineRecognitionSource.request_exact arity input false

def output (kind : Kind) (d : Data s arity) : Option WitnessOutput.Output :=
  WitnessOutput.originalOutput (descriptors arity d.input) (descriptorValid arity d)
    (body arity kind d.input) (address arity kind)

/-- The programme depends only on the class tag, never on its accepted result. -/
def machine (kind : Kind) : BinaryCompose.Machine :=
  (prepare kind).machine.compose WitnessOutput.originalMachine

theorem outputs (kind : Kind) (d : Data s arity) : ∃ ticks,
    Nonempty (TM2OutputsInTime (machine kind).computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (WitnessOutput.resultEncoding.encode (output arity kind d))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := WitnessOutput.original_outputs
    (descriptors arity d.input) (descriptorValid arity d) (body arity kind d.input) (address arity kind)
  have left := (prepare kind).outputs (original arity d)
  rw [original,request_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

def answer (kind : Kind) (d : Data s arity) : Bool :=
  match kind with
  | .affine => UniformTractXSemantics.affine arity d
  | .product => UniformTractXSemantics.product arity d
  | .localAffine => UniformTractXSemantics.localAffine arity d

theorem output_isSome (kind : Kind) (d : Data s arity) :
    (output arity kind d).isSome = true ↔ answer arity kind d = true := by
  rw [output,WitnessOutput.originalOutput_isSome]
  cases kind <;> rfl

def target : Kind → SignatureFamily AlgebraicComplex
  | .affine => affineClass
  | .product => productClass
  | .localAffine => localAffineClass

theorem output_correct (kind : Kind) (d : Data s arity) :
    (output arity kind d).isSome = true ↔ CommonTransformable (target kind) (AffineBranch.indexedFamily d.G) := by
  rw [output_isSome]
  cases kind with
  | affine => exact UniformTractXSemantics.affine_correct arity d
  | product => exact UniformTractXSemantics.product_correct arity d
  | localAffine => exact UniformTractXSemantics.localAffine_correct arity d

theorem none_iff (kind : Kind) (d : Data s arity) :
    output arity kind d = none ↔ ¬ CommonTransformable (target kind) (AffineBranch.indexedFamily d.G) := by
  rw [← output_correct arity kind d]
  cases output arity kind d <;> simp

/-- Returned coordinates satisfy every original binding and every literal
polynomial in the generated raw system. They belong to the very candidate
serialized by this run, not a newly chosen witness after a Boolean decision. -/
theorem returned_sound (kind : Kind) (d : Data s arity) (o : WitnessOutput.Output)
    (ho : output arity kind d = some o) :
    ∃ c : OriginalSystemWitness.Candidate (m:=Entries arity+2) (body arity kind d.input),
      OriginalSystemWitness.candidate (descriptors arity d.input) (descriptorValid arity d)
        (body arity kind d.input) (address arity kind) = some c ∧
      o = WitnessOutput.ofCandidate c ∧ ∃ θ : AlgebraicComplex, o.root.Represents (θ : ℂ) ∧
      (∀ i, (PowerArithmetic.decode θ (c.1.2.2.2.2 (address arity kind i)) : ℂ) =
        (UniformKPolynomial.values arity d.G i : ℂ)) ∧
      ∀ p ∈ body arity kind d.input,
        SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
          (fun i => (PowerArithmetic.decode θ (c.1.2.2.2.2 i) : ℂ)) p = 0 := by
  obtain ⟨c,hc,ho,θ,hθ,_,_,hb,he⟩ := WitnessOutput.original_returned_sound
    (descriptors arity d.input) (descriptorValid arity d) (UniformKPolynomial.values arity d.G)
    (UniformKPolynomial.descriptors_represents arity d.G d.input d.represented)
    (body arity kind d.input) (address arity kind) o ho
  exact ⟨c,hc,ho,θ,hθ,hb,he⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTractXWitness
