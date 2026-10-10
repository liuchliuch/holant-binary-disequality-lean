import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.StructuralChoicesMachine
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineBranchSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineFamilyEnumeration
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open ComplexIsolation.RootSearchDriver (cross mem_cross)

abbrev Template := EncodedTable.Data
abbrev Family := OriginalCatalogueMachine.Family
abbrev choicesEncoding := framedListEncoding RawAffineEnumeration.outputEncoding
abbrev candidateEncoding := RawAffineBranchMachine.templatesEncoding
abbrev candidatesEncoding := framedListEncoding candidateEncoding

def prependChoices (xs : List Template) (rest : List (List Template)) : List (List Template) :=
  (cross xs rest).map (fun p => p.1::p.2)
def product (choices : List (List Template)) : List (List Template) := choices.foldr prependChoices [[]]
def choices (xs : Family) : List (List Template) := xs.map (fun v => RawAffineEnumeration.templates v.1)
def candidates (xs : Family) : List RawAffineBranchMachine.Templates :=
  cross (product (choices xs)) (RawAffineEnumeration.templates 2)

theorem product_nil : product []=[[]] := rfl
theorem product_cons (xs : List Template) (choices : List (List Template)) :
    product (xs::choices)=prependChoices xs (product choices) := rfl

theorem mem_product {cs : List (List Template)} {ts : List Template}
    (h : List.Forall₂ (fun c t => t ∈ c) cs ts) : ts ∈ product cs := by
  induction h with
  | nil => simp [product]
  | @cons c t cs ts hc ht ih =>
    exact List.mem_map.mpr ⟨(t,ts),mem_cross.mpr ⟨hc,ih⟩,rfl⟩

theorem mem_product_iff (cs : List (List Template)) (ts : List Template) :
    ts ∈ product cs ↔ List.Forall₂ (fun c t => t ∈ c) cs ts := by
  constructor
  · intro h
    induction cs generalizing ts with
    | nil =>
      have he : ts=[] := by simpa only [product_nil,List.mem_singleton] using h
      subst ts
      exact .nil
    | cons c cs ih =>
      obtain ⟨⟨t,rest⟩,hp,rfl⟩ := List.mem_map.mp h
      obtain ⟨ht,hr⟩ := mem_cross.mp hp
      exact .cons ht (ih rest hr)
  · exact mem_product

variable {s : ℕ} (arity : Fin s → ℕ)
theorem source_mem (input : OriginalFamilyInput.Input arity) (B : AffineBranch.Branch arity) :
    ((RawAffineBranchSource.fromSource arity input true B).2) ∈
      candidates (OriginalCatalogueSource.family arity input) := by
  apply mem_cross.mpr
  refine ⟨mem_product ?_,RawAffineEnumeration.source_mem B.2⟩
  change List.Forall₂ (fun c t => t ∈ c)
    (((List.finRange s).map (fun i => (arity i,(SparseTransform.allWords (arity i)).map (input i)))).map
      (fun v => RawAffineEnumeration.templates v.1))
    (List.ofFn (fun i => RationalAffineTemplateSource.sourceCode (B.1 i)))
  rw [List.map_map,List.ofFn_eq_map]
  have h : ∀ is : List (Fin s), List.Forall₂ (fun c t => t ∈ c)
      (is.map (fun i => RawAffineEnumeration.templates (arity i)))
      (is.map (fun i => RationalAffineTemplateSource.sourceCode (B.1 i))) := by
    intro is
    induction is with
    | nil => exact .nil
    | cons i is ih => exact .cons (RawAffineEnumeration.source_mem (B.1 i)) ih
  exact h _

noncomputable section

def prependComputes : Computes
    (pairEncoding RawAffineEnumeration.outputEncoding choicesEncoding) choicesEncoding
    (fun p => prependChoices p.1 p.2) :=
  StructuralChoicesMachine.prependComputes EncodedTable.encoding

def productExecutes : Executes choicesEncoding choicesEncoding product :=
  StructuralChoicesMachine.executes EncodedTable.encoding

def choicesExecutes : Executes OriginalCatalogueMachine.familyEncoding choicesEncoding choices := by
  let vertex : Executes OriginalFamilyPackingMachine.vertexEncoding RawAffineEnumeration.outputEncoding
      (fun v => RawAffineEnumeration.templates v.1) :=
    (Executes.ofComputes (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding)).comp
      RawAffineEnumeration.executes
  let cell := (Executes.ofComputes
    (Wiring.secondComputes OriginalCatalogueMachine.familyEncoding OriginalFamilyPackingMachine.vertexEncoding)).comp vertex
  exact NegativeCertificateMachine.Lists.map OriginalCatalogueMachine.familyEncoding
    OriginalFamilyPackingMachine.vertexEncoding RawAffineEnumeration.outputEncoding
    (Executes.ofComputes (identityComputes OriginalCatalogueMachine.familyEncoding))
    (fun _ v => RawAffineEnumeration.templates v.1) cell

def executes : Executes OriginalCatalogueMachine.familyEncoding candidatesEncoding candidates := by
  let edge := (Executes.ofComputes (constantComputes OriginalCatalogueMachine.familyEncoding encodingNatBool 2)).comp
    RawAffineEnumeration.executes
  exact ((choicesExecutes.comp productExecutes).pair edge).comp
    (Executes.ofComputes (ComplexIsolation.RootSearchDriver.crossComputes
      RawAffineEnumeration.outputEncoding EncodedTable.encoding))

def outputs (xs : Family) : TM2OutputsInTime executes.machine.computer
    (OriginalCatalogueMachine.familyEncoding.encode xs)
    (some (candidatesEncoding.encode (candidates xs))) (executes.cost xs) := executes.outputs xs
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineFamilyEnumeration
