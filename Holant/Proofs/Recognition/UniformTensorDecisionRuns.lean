import Holant.Proofs.Recognition.UniformTensorDecisionBranch
import Holant.Proofs.Recognition.PhysicalFolds

/-! Operational wrappers around the actual original-descriptor branch programmes.
Only the existing physical all/any fold combinators consume these wrappers. -/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecisionBranch
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
open PolynomialDecision
noncomputable section
variable {s : ℕ} (arity : Fin s → ℕ)

def groundRuns (e : Expr (Count arity)) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity) (ground arity e) where
  machine := groundMachine arity e
  cost d := Classical.choose (ground_outputs arity e d)
  outputs d := Classical.choice (Classical.choose_spec (ground_outputs arity e d))


variable {n : ℕ}

def branchRuns (oneHot : Bool) (entries : (Fin n → Bool) → Expr (Count arity))
    (count : ℕ) (sizes : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (sizes i)) ≃ Fin n) (pivot : Fin n → Bool) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity)
      (branchAnswer arity oneHot entries count sizes ports pivot) where
  machine := branchMachine arity oneHot entries count sizes ports pivot
  cost d := Classical.choose (branch_outputs arity oneHot entries count sizes ports pivot d)
  outputs d := Classical.choice (Classical.choose_spec
    (branch_outputs arity oneHot entries count sizes ports pivot d))


end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecisionBranch
