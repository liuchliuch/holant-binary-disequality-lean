import Holant.Proofs.Reductions.RootPreprocessing.Raw
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionChoiceInterface
import Holant.Proofs.BinaryInterpolation.SingularExtraction.GroupingMachine


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace RowProgram
variable {s b : ℕ} {a : ℕ → ℕ}

/-- A semantic row flatMap obtains a machine only from a real encoded provider.
Every variable-length traversal is the existing ContextFlatMap machine. -/
def computes (f : RawVertex → List RawVertex)
    (provider : Computes (queryEncoding s b a) Frame.wordEncoding
      (fun x => entries vertexEncoding (f (x.1.val.vertices.get x.2)))) :
    Computes (validatedEncoding s b a) (framedListEncoding vertexEncoding)
      (fun r => r.val.vertices.flatMap f) := by
  let run := allRowsFlatMapComputes s b a _ provider
  refine recode (joinComputes run (constantComputes _ Frame.wordEncoding [false])) id
    (fun _ => rfl) ?_
  intro r
  have hall := congrArg (fun rows : List RawVertex => rows.flatMap
    (fun row => entries vertexEncoding (f row))) (all_rows s b a r)
  simp only [List.flatMap_map] at hall
  change _ ++ [false] = _
  dsimp only [id_eq]
  rw [hall]
  have he : r.val.vertices.flatMap (fun row => entries vertexEncoding (f row)) =
      entries vertexEncoding (r.val.vertices.flatMap f) := by
    simp only [entries,List.flatMap_assoc]
  rw [he]
  have h := entries_append_encode vertexEncoding (r.val.vertices.flatMap f) []
  simp only [List.append_nil] at h
  exact h

end RowProgram

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def cleanTestComputes : Computes (sourceEncoding (s:=s) (a:=a)) encodingBoolBool
    (fun r => decide (Clean G r.val)) :=
  congrComputes ((pairComputes (fullWeightComputes s 1 a (deadWeight G))
    (constantComputes _ UnaryBinary.unaryEncoding 0)).andThen (equalComputes UnaryBinary.unaryEncoding))
    (fun r => by simp [Clean,zeroCount])

def goodEncoding : Encoding (GoodInput G) Bool where
  encode r := (sourceEncoding (s:=s) (a:=a)).encode r.val
  decode bits := do
    let r ← (sourceEncoding (s:=s) (a:=a)).decode bits
    if h : Clean G r.val then some ⟨r,h⟩ else none
  decode_encode r := by simp [r.property]

/-- All candidates here are total byte copies or fixed tags. No surgery is
executed here, and the proof refinement is justified by the computed test. -/
def selectComputes : Computes (sourceEncoding (s:=s) (a:=a))
    (optionEncoding (goodEncoding G)) (select G) := by
  let someWord := joinComputes (constantComputes (sourceEncoding (s:=s) (a:=a))
    Frame.wordEncoding [true]) (encodeComputes (sourceEncoding (s:=s) (a:=a)))
  let run := ifComputes (cleanTestComputes G) someWord
    (constantComputes (sourceEncoding (s:=s) (a:=a)) Frame.wordEncoding [false])
  refine recode run id (fun _ => rfl) ?_
  intro r
  by_cases h : Clean G r.val <;> simp [select,h,optionEncoding,goodEncoding,Frame.wordEncoding]

def chunkComputes : Computes (queryEncoding s 1 a) Frame.wordEncoding
    (fun x => entries vertexEncoding (rowChunk G (x.1.val.vertices.get x.2))) := by
  let candidates (x : Query s 1 a) (i : Fin s) :=
    if Keep G i then entry vertexEncoding (compactNat G i.val,(x.1.val.vertices.get x.2).2) else []
  let provider (i : Fin s) : Computes (queryEncoding s 1 a) Frame.wordEncoding
      (fun x => candidates x i) := by
    by_cases h : Keep G i
    · let row : Computes (queryEncoding s 1 a) vertexEncoding
          (fun x => (compactNat G i.val,(x.1.val.vertices.get x.2).2)) :=
        recode (pairComputes (constantComputes (queryEncoding s 1 a)
        encodingNatBool (compactNat G i.val)) (GroupingMachine.rowPortsComputes s 1 a))
        id (fun _ => rfl) (fun _ => rfl)
      exact congrComputes (row.andThen (entryComputes vertexEncoding))
        (fun x => by simp [candidates,h])
    · exact congrComputes (constantComputes _ Frame.wordEncoding [])
        (fun x => by simp [candidates,h])
  refine congrComputes (chooseComputes (queryEncoding s 1 a) Frame.wordEncoding s
    (sourceLabel s 1 a) candidates
    (labelRecodeComputes s 1 a UnaryBinary.unaryEncoding Fin.val) provider) ?_
  intro x
  have hl : (x.1.val.vertices.get x.2).1 < s := (x.1.property.1 x.2).1
  have hkeep : keepNat G (x.1.val.vertices.get x.2).1 ↔
      Keep G ⟨(x.1.val.vertices.get x.2).1,hl⟩ := by
    simp only [keepNat]
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨hl,h⟩⟩
  change (if Keep G ⟨(x.1.val.vertices.get x.2).1,hl⟩ then
      entry vertexEncoding (compactNat G (x.1.val.vertices.get x.2).1,
        (x.1.val.vertices.get x.2).2) else []) = _
  unfold rowChunk
  rw [hkeep]
  split_ifs <;> simp [entries]

/-- The raw compiler is total, but is certified as a closed retained graph
only on GoodInput. Its execution occurs only after optional selection. -/
def strippedComputes : Computes (sourceEncoding (s:=s) (a:=a)) RawClosedNetwork.encoding
    (fun r => stripped G r.val) :=
  recode (pairComputes (RowProgram.computes (rowChunk G) (chunkComputes G))
    (edgesComputes s 1 a)) id (fun _ => rfl) (fun _ => rfl)

def cleanQueryComputes : Computes (goodEncoding G)
    (validatedEncoding (count G) 1 (targetArity G)) (cleanQuery G) :=
  recode (strippedComputes G) Subtype.val (fun _ => rfl) (fun _ => rfl)

def optionalQueryComputes : Computes (sourceEncoding (s:=s) (a:=a))
    (optionEncoding (validatedEncoding (count G) 1 (targetArity G)))
    (fun r => (select G r).map (cleanQuery G)) :=
  (selectComputes G).andThen (OptionMap.computes (cleanQueryComputes G))

/-- Turn the optional encoded answer into an encoded total answer, physically
copying a present word and emitting the fixed fallback on absence. -/
def getOptionComputes {B : Type} (e : Encoding B Bool) (fallback : B) :
    Computes (optionEncoding e) e (fun x => x.getD fallback) := by
  let words : Computes (optionEncoding e) (optionEncoding Frame.wordEncoding)
      (fun x => x.map e.encode) := recode (identityComputes (optionEncoding e)) id
        (fun _ => rfl) (fun x => by cases x <;> rfl)
  let run := (pairComputes words (constantComputes (optionEncoding e)
    (optionEncoding Frame.wordEncoding) none)).andThen (OptionChoice.computes (e.encode fallback))
  exact recode run id (fun _ => rfl) (fun x => by cases x <;> rfl)

def queryComputes : Computes (sourceEncoding (s:=s) (a:=a))
    (validatedEncoding (count G) 1 (targetArity G)) (query G) :=
  (optionalQueryComputes G).andThen
    (getOptionComputes (validatedEncoding (count G) 1 (targetArity G)) (emptyQuery G))

/-- This is the actual provider wrapper, not an eager if/choose wrapper. -/
theorem zero_provider_run :
    RunsExactly (OptionMap.machine (cleanQueryComputes G).machine).computer.step
      (Turing.initList (OptionMap.machine (cleanQueryComputes G).machine).computer [false])
      (Turing.haltList (OptionMap.machine (cleanQueryComputes G).machine).computer [false]) 2 :=
  OptionMap.none_exact (cleanQueryComputes G).machine

end Holant.LocalDrafts.Hardness.RootPreprocessing
