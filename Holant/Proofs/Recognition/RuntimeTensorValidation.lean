import Holant.Proofs.Recognition.RuntimeTensorCatalogue
import Holant.Proofs.Algorithms.TransformRecognition.ProductAllocationMachine

/-!
# Physical checks on runtime ordered tensor candidates

One finite programme checks the generated candidate's block sum, permitted
positive block sizes, and coverage of every original port. Completeness and
semantic reification are separate from the algebraic row test, which this
module does not claim to execute.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorValidation
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open FixedGadgetSubstitution.Compiler
open UniformTensorWitnessBranch (Metadata metadata metadataEncoding natListEncoding)

abbrev Input := Bool × (ℕ × Metadata)
abbrev tailEncoding := pairEncoding encodingNatBool metadataEncoding
abbrev encoding := pairEncoding encodingBoolBool tailEncoding

def allowed (oneHot : Bool) (k : ℕ) : Bool :=
  if oneHot then !decide (k=0) else decide (k=1) || decide (k=2)

def member (j : ℕ) (ports : List ℕ) : Bool := ports.any (fun k => decide (j=k))
def covers (n : ℕ) (ports : List ℕ) : Bool := (List.range n).all (fun j => member j ports)

def valid (r : Input) : Bool :=
  decide (r.2.2.1.sum=r.2.1) && r.2.2.1.all (allowed r.1) && covers r.2.1 r.2.2.2.1

theorem allowed_true (k : ℕ) : allowed true k=true ↔ 0<k := by
  cases k <;> simp [allowed]

theorem allowed_false (k : ℕ) : allowed false k=true ↔ k=1 ∨ k=2 := by
  simp [allowed]

theorem member_correct (j : ℕ) (ports : List ℕ) : member j ports=true ↔ j∈ports := by
  simp [member,List.any_eq_true]

theorem covers_correct (n : ℕ) (ports : List ℕ) :
    covers n ports=true ↔ ∀j<n,j∈ports := by
  simp only [covers,List.all_eq_true,List.mem_range,member_correct]

theorem valid_correct (oneHot : Bool) (n : ℕ) (m : Metadata) :
    valid (oneHot,n,m)=true ↔ m.1.sum=n ∧ (∀k∈m.1,allowed oneHot k=true) ∧
      ∀j<n,j∈m.2.1 := by
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,covers_correct,and_assoc]

/-- Every genuine ordered shape passes the physical metadata check. -/
theorem source_valid {n count : ℕ} (oneHot : Bool) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) (ha : ∀ i, allowed oneHot (arity i)=true) :
    valid (oneHot,n,metadata count arity ports pivot)=true := by
  apply (valid_correct oneHot n _).mpr
  constructor
  · have h := Fintype.card_congr ports
    simpa only [metadata,List.sum_ofFn,Fintype.card_sigma,Fintype.card_fin] using h
  constructor
  · intro k hk
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
    exact ha i
  · intro j hj
    obtain ⟨⟨i,k⟩,h⟩ := ports.surjective ⟨j,hj⟩
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_finRange i,List.mem_map.mpr ⟨k,List.mem_finRange k,?_⟩⟩
    exact congrArg Fin.val h

theorem arity_shape_valid {n : ℕ} (S : TensorDecision.Shape n) (pivot : Fin n → Bool) :
    valid (false,n,metadata S.count S.arity S.ports pivot)=true :=
  source_valid false S.arity S.ports pivot (fun i => (allowed_false _).mpr (S.allowed i))

theorem matching_shape_valid {n : ℕ} (S : TensorDecisionStable.Shape n) (pivot : Fin n → Bool) :
    valid (true,n,metadata S.count S.arity S.ports pivot)=true :=
  source_valid true S.arity S.ports pivot (fun i => (allowed_true _).mpr (S.positive i))

noncomputable section

def allowedComputes : Computes (pairEncoding encodingBoolBool encodingNatBool)
    encodingBoolBool (fun p => allowed p.1 p.2) := by
  let b := Wiring.firstComputes encodingBoolBool encodingNatBool
  let k := Wiring.secondComputes encodingBoolBool encodingNatBool
  let test (n : ℕ) := (pairComputes k (constantComputes (pairEncoding encodingBoolBool encodingNatBool)
    encodingNatBool n)).andThen (equalComputes encodingNatBool)
  let neg := FiniteRecode.computes encodingBoolBool encodingBoolBool Bool.not 1 (fun b => by cases b <;> decide)
  let op := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 || p.2)
  exact ifComputes b ((test 0).andThen neg) ((pairComputes (test 1) (test 2)).andThen op)

def memberComputes : Computes (pairEncoding encodingNatBool natListEncoding) encodingBoolBool
    (fun p => member p.1 p.2) :=
  congrComputes ((mapListComputes encodingNatBool encodingNatBool encodingBoolBool
    (fun j k => decide (j=k)) (equalComputes encodingNatBool)).andThen ResidueCells.any)
    (fun p => by simp only [member,List.any_map,Function.comp_def,id_eq])

abbrev coverEncoding := pairEncoding encodingNatBool natListEncoding

def coversExecutes : Executes coverEncoding encodingBoolBool (fun p => covers p.1 p.2) := by
  let n := Wiring.firstComputes encodingNatBool natListEncoding
  let ps := Wiring.secondComputes encodingNatBool natListEncoding
  let indices := (Executes.ofComputes n).comp RationalInputMachine.Programs.range
  let p := Wiring.firstComputes coverEncoding encodingNatBool
  let j := Wiring.secondComputes coverEncoding encodingNatBool
  let cell := (pairComputes j (p.andThen ps)).andThen memberComputes
  exact ((NegativeCertificateMachine.Lists.map coverEncoding encodingNatBool encodingBoolBool indices
    (fun p j => member j p.2) (Executes.ofComputes cell)).comp (Executes.ofComputes ResidueCells.all)).congr
      (fun p => by simp only [covers,List.all_map,Function.comp_def,id_eq])

def executes : Executes encoding encodingBoolBool valid := by
  let mode := Wiring.firstComputes encodingBoolBool tailEncoding
  let tail := Wiring.secondComputes encodingBoolBool tailEncoding
  let n := tail.andThen (Wiring.firstComputes encodingNatBool metadataEncoding)
  let record :=  tail.andThen (Wiring.secondComputes encodingNatBool metadataEncoding)
  let sizes := record.andThen (Wiring.firstComputes natListEncoding
    (pairEncoding natListEncoding (framedListEncoding encodingBoolBool)))
  let ports := (record.andThen (Wiring.secondComputes natListEncoding
    (pairEncoding natListEncoding (framedListEncoding encodingBoolBool)))).andThen
      (Wiring.firstComputes natListEncoding (framedListEncoding encodingBoolBool))
  let sum := ((Executes.ofComputes sizes).comp ProductAllocationMachine.sumExecutes).pair (Executes.ofComputes n)
  let sumTest := sum.comp (Executes.ofComputes (equalComputes encodingNatBool))
  let sizeTests := ((pairComputes mode sizes).andThen
    (mapListComputes encodingBoolBool encodingNatBool encodingBoolBool allowed allowedComputes)).andThen ResidueCells.all
  let coverage := (Executes.ofComputes (pairComputes n ports)).comp coversExecutes
  let op := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2)
  exact ((((sumTest.pair (Executes.ofComputes sizeTests)).comp (Executes.ofComputes op)).pair coverage).comp
    (Executes.ofComputes op)).congr (fun r => by simp only [valid,List.all_map,Function.comp_def,id_eq])

def source_outputs (r : Input) : TM2OutputsInTime executes.machine.computer
    (encoding.encode r) (some (encodingBoolBool.encode (valid r))) (executes.cost r) := executes.outputs r

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorValidation
