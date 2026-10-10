import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.StructuralChoicesMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineFamilyEnumeration
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Family := OriginalCatalogueMachine.Family
abbrev Candidate := List RawLocalAffineEnumeration.Candidate
abbrev candidateEncoding := framedListEncoding RawLocalAffineEnumeration.candidateEncoding
abbrev outputEncoding := framedListEncoding candidateEncoding

def choices (xs : Family) : List (List RawLocalAffineEnumeration.Candidate) :=
  (OriginalCatalogueMachine.extended xs).map (fun v => RawLocalAffineEnumeration.candidates v.1)
def candidates (xs : Family) : List Candidate := StructuralChoicesMachine.product (choices xs)

theorem generated_relation (xs : Family) (c : Candidate) (hc : c ∈ candidates xs) :
    List.Forall₂ (fun ds d => d ∈ ds) (choices xs) c :=
  (StructuralChoicesMachine.mem_product_iff _ _).mp hc

theorem generated_length (xs : Family) (c : Candidate) (hc : c ∈ candidates xs) :
    c.length=xs.length+1 := by
  have h := (generated_relation xs c hc).length_eq
  simpa only [choices,OriginalCatalogueMachine.extended,List.length_map,List.length_append,
    List.length_cons,List.length_nil,Nat.add_zero] using h.symm

noncomputable section

def choicesExecutes : Executes OriginalCatalogueMachine.familyEncoding outputEncoding choices := by
  let vertex : Executes OriginalFamilyPackingMachine.vertexEncoding RawLocalAffineEnumeration.outputEncoding
      (fun v => RawLocalAffineEnumeration.candidates v.1) :=
    (Executes.ofComputes (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding)).comp
      RawLocalAffineEnumeration.executes
  let cell := (Executes.ofComputes
    (Wiring.secondComputes OriginalCatalogueMachine.familyEncoding OriginalFamilyPackingMachine.vertexEncoding)).comp vertex
  exact NegativeCertificateMachine.Lists.map OriginalCatalogueMachine.familyEncoding
    OriginalFamilyPackingMachine.vertexEncoding RawLocalAffineEnumeration.outputEncoding
    (Executes.ofComputes OriginalCatalogueMachine.extendedComputes)
    (fun _ v => RawLocalAffineEnumeration.candidates v.1) cell

def executes : Executes OriginalCatalogueMachine.familyEncoding outputEncoding candidates :=
  choicesExecutes.comp (StructuralChoicesMachine.executes RawLocalAffineEnumeration.candidateEncoding)
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineFamilyEnumeration
