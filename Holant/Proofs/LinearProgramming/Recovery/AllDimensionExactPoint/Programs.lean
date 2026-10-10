import Holant.Proofs.LinearProgramming.LowDimension.Programs
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Source

/-! All-dimension eager dispatch with a physical legal fallback. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.AllDimensionExactPoint
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.OneHot.StackProgram.GraphLabelEncoding
open GraphPreprocessing
open Holant.LocalDrafts.RemoteWork.RationalLP Foundation Support.MachineCombinators

namespace Programs
noncomputable section
attribute [local irreducible] LowDimension.Programs.zeroTyped
  LowDimension.Programs.oneTyped SuccessiveFaceMachine.Source.computes

def dimensionIs (n : ℕ) : Computes Codec.inputEncoding encodingBoolBool
    (fun d => decide (d.val.dimension=n)) :=
  recode ((pairComputes Foundation.Parsing.dimension
    (constantComputes Codec.encoding UnaryBinary.unaryEncoding n)).andThen
    Foundation.Parsing.unaryEqual) Subtype.val (fun _ => rfl) (fun _ => rfl)
def fallback : Codec.Input := ⟨⟨0,2,[],[]⟩,by simp [Codec.Raw.WellFormed]⟩
def prepareInput (d : Codec.Input) : SuccessiveFaceMachine.Source.Input :=
  if h0 : d.val.dimension=0 then ⟨fallback,by decide⟩
  else if h1 : d.val.dimension=1 then ⟨fallback,by decide⟩
  else ⟨d,by omega⟩
def prepareComputes : Computes Codec.inputEncoding SuccessiveFaceMachine.Source.inputEncoding
    prepareInput := by
  let c := constantComputes Codec.inputEncoding Codec.inputEncoding fallback
  let w := ifComputes (dimensionIs 0) c
    (ifComputes (dimensionIs 1) c (identityComputes Codec.inputEncoding))
  refine recode w id (fun _ => rfl) ?_
  intro d
  by_cases h0 : d.val.dimension=0
  · simp [SuccessiveFaceMachine.Source.inputEncoding, SuccessiveFaceMachine.inputEncoding,
      prepareInput,h0]
  · by_cases h1 : d.val.dimension=1 <;>
      simp [SuccessiveFaceMachine.Source.inputEncoding, SuccessiveFaceMachine.inputEncoding,
        prepareInput,h0,h1]

theorem prepared_original (d : Codec.Input) (hn : 2≤d.val.dimension) :
    (prepareInput d).val=d := by
  have h0 : d.val.dimension≠0 := by omega
  have h1 : d.val.dimension≠1 := by omega
  simp [prepareInput,h0,h1]
theorem prepared_original_bytes (d : Codec.Input) (hn : 2≤d.val.dimension) :
    SuccessiveFaceMachine.Source.inputEncoding.encode (prepareInput d)=Codec.inputEncoding.encode d := by
  simp only [SuccessiveFaceMachine.Source.original_bytes,prepared_original d hn]

def highComputes : Computes Codec.inputEncoding Codec.outputEncoding
    (fun d => SuccessiveFaceMachine.Source.value (prepareInput d)) :=
  prepareComputes.andThen SuccessiveFaceMachine.Source.computes
def top (d : Codec.Input) : Option (List ℚ) :=
  if d.val.dimension=0 then LowDimension.ZeroDim.value d.val
  else if d.val.dimension=1 then LowDimension.OneDim.value d.val
  else SuccessiveFaceMachine.Source.value (prepareInput d)
private theorem tested_value_eq {A : Type} (n : ℕ) (zero one high : A) :
    (if decide (n=0) then zero else if decide (n=1) then one else high)=
      (if n=0 then zero else if n=1 then one else high) := by
  by_cases h0 : n=0
  · simp [h0]
  · by_cases h1 : n=1 <;> simp [h0,h1]
def computes : Computes Codec.inputEncoding Codec.outputEncoding top := by
  refine congrComputes (ifComputes (dimensionIs 0) LowDimension.Programs.zeroTyped
    (ifComputes (dimensionIs 1) LowDimension.Programs.oneTyped highComputes)) ?_
  intro d
  simpa only [top] using tested_value_eq d.val.dimension (LowDimension.ZeroDim.value d.val) (LowDimension.OneDim.value d.val)
    (SuccessiveFaceMachine.Source.value (prepareInput d))

theorem zero_branch (d : Codec.Input) (hn : d.val.dimension=0) :
    top d=LowDimension.ZeroDim.value d.val := by simp only [top,if_pos hn]
theorem one_branch (d : Codec.Input) (hn : d.val.dimension=1) :
    top d=LowDimension.OneDim.value d.val := by
  have h0 : d.val.dimension≠0 := by omega
  simp only [top,if_neg h0,if_pos hn]
theorem high_branch (d : Codec.Input) (hn : 2≤d.val.dimension) :
    top d=SuccessiveFaceMachine.Source.value (prepareInput d) := by
  have h0 : d.val.dimension≠0 := by omega
  have h1 : d.val.dimension≠1 := by omega
  simp only [top,if_neg h0,if_neg h1]

end
end Programs
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.AllDimensionExactPoint
