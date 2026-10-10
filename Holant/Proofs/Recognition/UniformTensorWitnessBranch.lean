import Holant.Proofs.Recognition.UniformTractXDecision

/-!
# Serialized ordered tensor branches with their actual algebraic witnesses

The packet carries the block arities, every block's ordered original port index,
the original pivot bits, and the complete actual polynomial-search witness. The
latter retains all original coefficient bindings and the inverse-pivot coordinate.
No freshly selected decomposition or algebraic point replaces these bytes.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorWitnessBranch

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
open PolynomialDecision UniformTensorDecisionSyntax UniformTensorDecisionBranch PhysicalFolds
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Metadata := List ℕ × (List ℕ × List Bool)
abbrev Packet := Metadata × WitnessOutput.Output
abbrev natListEncoding := framedListEncoding encodingNatBool
abbrev metadataEncoding := pairEncoding natListEncoding (pairEncoding natListEncoding (framedListEncoding encodingBoolBool))
abbrev packetEncoding := pairEncoding metadataEncoding WitnessOutput.outputEncoding
abbrev resultEncoding := optionEncoding packetEncoding

variable {n : ℕ}

def metadata (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool) : Metadata :=
  (List.ofFn sizes,
    (List.finRange count).flatMap (fun i => (List.finRange (sizes i)).map (fun j => (ports ⟨i,j⟩).val)),
    List.ofFn pivot)

variable {s : ℕ} (arity : Fin s → ℕ)

def raw (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) : Option WitnessOutput.Output :=
  PolynomialDecision.witness (q:=1) (UniformKPolynomial.descriptors arity d.input)
    (UniformKPolynomial.valid arity d.G d.input d.represented)
    (branch oneHot entries count sizes ports pivot)

def rawMachine (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool) : BinaryCompose.Machine :=
  OriginalFamilyPackingMachine.rootsComputes.machine.compose
    (PolynomialDecision.witnessMachine (q:=1) (branch oneHot entries count sizes ports pivot))

theorem raw_outputs (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) : ∃ ticks,
    Nonempty (TM2OutputsInTime (rawMachine arity oneHot entries count sizes ports pivot).computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (WitnessOutput.resultEncoding.encode (raw arity oneHot entries count sizes ports pivot d))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := PolynomialDecision.witness_outputs (q:=1)
    (UniformKPolynomial.descriptors arity d.input)
    (UniformKPolynomial.valid arity d.G d.input d.represented)
    (branch oneHot entries count sizes ports pivot)
  have left := OriginalFamilyPackingMachine.rootsComputes.outputs (original arity d)
  rw [original,OriginalFamilyPackingSource.roots_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem raw_isSome_iff (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) :
    (raw arity oneHot entries count sizes ports pivot d).isSome = true ↔
      branchAnswer arity oneHot entries count sizes ports pivot d = true :=
  WitnessOutput.originalOutput_isSome _ _ _ _

def rawRuns (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool) :
    Runs OriginalFamilyPackingMachine.encoding WitnessOutput.resultEncoding (original arity)
      (raw arity oneHot entries count sizes ports pivot) where
  machine := rawMachine arity oneHot entries count sizes ports pivot
  cost d := Classical.choose (raw_outputs arity oneHot entries count sizes ports pivot d)
  outputs d := Classical.choice (Classical.choose_spec
    (raw_outputs arity oneHot entries count sizes ports pivot d))

def output (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) : Option Packet :=
  (raw arity oneHot entries count sizes ports pivot d).map (fun o => (metadata count sizes ports pivot,o))

def runs (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool) :
    Runs OriginalFamilyPackingMachine.encoding resultEncoding (original arity)
      (output arity oneHot entries count sizes ports pivot) :=
  (rawRuns arity oneHot entries count sizes ports pivot).after
    (OptionMap.computes (pairComputes
      (constantComputes WitnessOutput.outputEncoding metadataEncoding (metadata count sizes ports pivot))
      (identityComputes WitnessOutput.outputEncoding)))

theorem output_isSome_iff (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) :
    (output arity oneHot entries count sizes ports pivot d).isSome = true ↔
      branchAnswer arity oneHot entries count sizes ports pivot d = true := by
  simp only [output,Option.isSome_map,raw_isSome_iff]

theorem output_metadata (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) (p : Packet)
    (hp : output arity oneHot entries count sizes ports pivot d = some p) :
    p.1 = metadata count sizes ports pivot ∧ raw arity oneHot entries count sizes ports pivot d = some p.2 := by
  obtain ⟨o,ho,hp⟩ := Option.map_eq_some_iff.mp hp
  cases hp
  exact ⟨rfl,ho⟩

/-- The literal emitted root coordinates satisfy the input bindings and every
branch expression, including the nonzero-pivot inverse guard. -/
theorem raw_returned_sound (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool)
    (d : Data s arity) (o : WitnessOutput.Output)
    (ho : raw arity oneHot entries count sizes ports pivot d = some o) :
    ∃ c : OriginalSystemWitness.Candidate (m:=Count arity)
        (PolynomialDecision.body (branch oneHot entries count sizes ports pivot)),
      OriginalSystemWitness.candidate (UniformKPolynomial.descriptors arity d.input)
        (UniformKPolynomial.valid arity d.G d.input d.represented)
        (PolynomialDecision.body (branch oneHot entries count sizes ports pivot))
        PolynomialDecision.address = some c ∧ o = WitnessOutput.ofCandidate c ∧
      ∃ θ : AlgebraicComplex, o.root.Represents (θ : ℂ) ∧
        (∀ i, (PowerArithmetic.decode θ (c.1.2.2.2.2 (PolynomialDecision.address i)) : ℂ) =
          (UniformKPolynomial.values arity d.G i : ℂ)) ∧
        ∀ e ∈ branch oneHot entries count sizes ports pivot,
          e.eval (fun i => (PowerArithmetic.decode θ (c.1.2.2.2.2 (Fin.natAdd 5 i)) : ℂ)) = 0 := by
  obtain ⟨c,hc,ho,θ,hθ,_,_,hb,he⟩ := WitnessOutput.original_returned_sound
    (UniformKPolynomial.descriptors arity d.input)
    (UniformKPolynomial.valid arity d.G d.input d.represented)
    (UniformKPolynomial.values arity d.G)
    (UniformKPolynomial.descriptors_represents arity d.G d.input d.represented)
    (PolynomialDecision.body (branch oneHot entries count sizes ports pivot))
    PolynomialDecision.address o ho
  refine ⟨c,hc,ho,θ,hθ,hb,?_⟩
  intro e he_mem
  rw [← Expr.compile_eval (fun i => (PowerArithmetic.decode θ (c.1.2.2.2.2 i) : ℂ)) e]
  exact he _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e,he_mem,rfl⟩))

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorWitnessBranch
