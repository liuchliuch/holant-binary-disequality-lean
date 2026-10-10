import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumerationValidity
import Holant.Proofs.Algorithms.TransformRecognition.RationalLocalAffineRowsMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineEnumeration
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver (cross mem_cross)
open CommonFieldMachine (Executes)

abbrev Choice := Bool × EncodedTable.Data
abbrev Candidate := List Choice
abbrev choiceEncoding := pairEncoding encodingBoolBool EncodedTable.encoding
abbrev candidateEncoding := framedListEncoding choiceEncoding
abbrev outputEncoding := framedListEncoding candidateEncoding

def alphabet (n : ℕ) : List Choice := cross [false,true] (RawAffineEnumeration.templates n)
def candidates (n : ℕ) : List Candidate :=
  StructuralListMachine.exactLength (alphabet n) (RationalTableMachine.words n).length

noncomputable def source {n : ℕ} (B : LocalAffineNormalForm.Code n) : Candidate :=
  (SparseTransform.allWords n).map (fun a =>
    (decide (a ∈ B.1),RationalAffineTemplateSource.sourceCode (B.2 a)))

theorem map_mem_exact {A B : Type} (xs : List A) (ys : List B) (f : A → B)
    (hf : ∀ a ∈ xs, f a ∈ ys) : xs.map f ∈ StructuralListMachine.exactLength ys xs.length := by
  have h := RawAffineEnumeration.exact_mem ys (fun i : Fin xs.length => f (xs.get i))
    (fun i => hf _ (List.get_mem xs i))
  have he : List.ofFn (fun i : Fin xs.length => f (xs.get i)) = xs.map f := by
    calc
      _ = (List.ofFn xs.get).map f := (List.map_ofFn (f:=xs.get) (g:=f)).symm
      _ = xs.map f := by rw [List.ofFn_get]
  rwa [he] at h

theorem source_mem {n : ℕ} (B : LocalAffineNormalForm.Code n) : source B ∈ candidates n := by
  unfold candidates
  rw [RationalTableMachine.words_eq,List.length_map]
  apply map_mem_exact
  intro a ha
  exact mem_cross.mpr ⟨by cases decide (a ∈ B.1) <;> simp,
    RawAffineEnumeration.source_mem (B.2 a)⟩

theorem generated_length (n : ℕ) (c : Candidate) (hc : c ∈ candidates n) :
    c.length=(RationalTableMachine.words n).length :=
  (RawAffineEnumerationValidity.vector_spec _ _ c hc).1

theorem generated_regular (n : ℕ) (c : Candidate) (hc : c ∈ candidates n)
    (e : Choice) (he : e ∈ c) : e.2.1=n ∧ EncodedTable.Regular e.2 :=
  RawAffineEnumerationValidity.generated_regular n e.2
    (mem_cross.mp ((RawAffineEnumerationValidity.vector_spec _ _ c hc).2 e he)).2

noncomputable section

def alphabetExecutes : Executes encodingNatBool candidateEncoding alphabet :=
  ((Executes.ofComputes (constantComputes encodingNatBool
    (framedListEncoding encodingBoolBool) [false,true])).pair RawAffineEnumeration.executes).comp
      (Executes.ofComputes (Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver.crossComputes
        encodingBoolBool EncodedTable.encoding))

def executes : Executes encodingNatBool outputEncoding candidates := by
  let count := RationalTableMachine.wordsExecutes.comp (Executes.ofComputes
    ((WireLists.lengthComputes RationalTensorMachine.wordEncoding).andThen UnaryBinary.computes))
  exact (count.pair alphabetExecutes).comp (StructuralListMachine.exactExecutes choiceEncoding)

def outputs (n : ℕ) : TM2OutputsInTime executes.machine.computer
    (encodingNatBool.encode n) (some (outputEncoding.encode (candidates n))) (executes.cost n) :=
  executes.outputs n
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineEnumeration
