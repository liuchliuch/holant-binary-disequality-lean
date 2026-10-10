import Holant.Proofs.Algorithms.TransformRecognition.RawProductEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.StructuralChoicesMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawProductFamilyEnumeration
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open RootSearchDriver (cross mem_cross)

abbrev Template := List RationalProductTemplateMachine.Edge
abbrev Candidate := List Template × Template
abbrev Family := OriginalCatalogueMachine.Family
abbrev choicesEncoding := framedListEncoding RawProductEnumeration.outputEncoding
abbrev candidateEncoding := pairEncoding RawProductEnumeration.outputEncoding RawProductEnumeration.edgesEncoding
abbrev candidatesEncoding := framedListEncoding candidateEncoding

def choices (xs : Family) : List (List Template) := xs.map (fun v => RawProductEnumeration.templates v.1)
def candidates (xs : Family) : List Candidate :=
  cross (StructuralChoicesMachine.product (choices xs)) (RawProductEnumeration.templates 2)

noncomputable section
def choicesExecutes : Executes OriginalCatalogueMachine.familyEncoding choicesEncoding choices := by
  let vertex : Executes OriginalFamilyPackingMachine.vertexEncoding RawProductEnumeration.outputEncoding
      (fun v => RawProductEnumeration.templates v.1) :=
    (Executes.ofComputes (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding)).comp
      RawProductEnumeration.executes
  let cell := (Executes.ofComputes
    (Wiring.secondComputes OriginalCatalogueMachine.familyEncoding OriginalFamilyPackingMachine.vertexEncoding)).comp vertex
  exact NegativeCertificateMachine.Lists.map OriginalCatalogueMachine.familyEncoding
    OriginalFamilyPackingMachine.vertexEncoding RawProductEnumeration.outputEncoding
    (Executes.ofComputes (identityComputes OriginalCatalogueMachine.familyEncoding))
    (fun _ v => RawProductEnumeration.templates v.1) cell

def executes : Executes OriginalCatalogueMachine.familyEncoding candidatesEncoding candidates := by
  let vertices := choicesExecutes.comp (StructuralChoicesMachine.executes RawProductEnumeration.edgesEncoding)
  let edge := (Executes.ofComputes (constantComputes OriginalCatalogueMachine.familyEncoding encodingNatBool 2)).comp
    RawProductEnumeration.executes
  exact (vertices.pair edge).comp (Executes.ofComputes
    (RootSearchDriver.crossComputes RawProductEnumeration.outputEncoding RawProductEnumeration.edgesEncoding))
end

variable {s : ℕ} (arity : Fin s → ℕ)
noncomputable def sourceCode (B : ProductBranch.Branch arity) : Candidate :=
  (List.ofFn (fun i => (B (.inl i)).toList.map RationalProductTemplateSource.edgeCode),
    (B (.inr ())).toList.map RationalProductTemplateSource.edgeCode)

theorem source_mem (input : OriginalFamilyInput.Input arity) (B : ProductBranch.Branch arity) :
    sourceCode arity B ∈ candidates (OriginalCatalogueSource.family arity input) := by
  apply mem_cross.mpr
  refine ⟨(StructuralChoicesMachine.mem_product_iff _ _).mpr ?_,RawProductEnumeration.skeleton_mem _⟩
  change List.Forall₂ (fun c t => t ∈ c)
    (((List.finRange s).map (fun i => (arity i,(SparseTransform.allWords (arity i)).map (input i)))).map
      (fun v => RawProductEnumeration.templates v.1))
    (List.ofFn (fun i => (B (.inl i)).toList.map RationalProductTemplateSource.edgeCode))
  rw [List.map_map,List.ofFn_eq_map]
  have h : ∀ is : List (Fin s), List.Forall₂ (fun c t => t ∈ c)
      (is.map (fun i => RawProductEnumeration.templates (arity i)))
      (is.map (fun i => (B (.inl i)).toList.map RationalProductTemplateSource.edgeCode)) := by
    intro is
    induction is with
    | nil => exact .nil
    | cons i is ih => exact .cons (RawProductEnumeration.skeleton_mem _) ih
  exact h _

end Holant.LocalDrafts.MainChain.TransformRecognition.RawProductFamilyEnumeration
