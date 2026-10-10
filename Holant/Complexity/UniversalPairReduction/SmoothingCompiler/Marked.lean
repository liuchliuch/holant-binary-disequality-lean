import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators
import Holant.Complexity.UniversalPairReduction.Smoothing

/-! The unique marked binary row is extracted from the original vertex stream,
using the already verified list traversal and fixed source-label recoding. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s : ℕ) (arity : ℕ → ℕ)

def markedEnds (r : RawClosedNetwork) : List RawEndpoint :=
  (r.vertices.filter (fun row => row.1 == s)).flatMap Prod.snd

def markedChunk (row : RawVertex) : List Bool :=
  if row.1 == s then FixedGadgetSubstitution.Compiler.entries endpointEncoding row.2 else []

noncomputable def markedChunkComputes :
    Computes (FixedGadgetSubstitution.Compiler.queryEncoding (s+1) 1 (extendedArity s arity)) Frame.wordEncoding
      (fun x => markedChunk s (x.1.val.vertices.get x.2)) := by
  let e := FixedGadgetSubstitution.Compiler.queryEncoding (s+1) 1 (extendedArity s arity)
  let test := FixedGadgetSubstitution.Compiler.labelRecodeComputes (s+1) 1 (extendedArity s arity)
    encodingBoolBool (fun i => i.val == s)
  let ends : Computes e (framedListEncoding endpointEncoding)
      (fun x => (x.1.val.vertices.get x.2).2) :=
    (FixedGadgetSubstitution.Compiler.originalRowComputes (s+1) 1 (extendedArity s arity)).andThen
      (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
        id (fun _ => rfl) (fun _ => rfl))
  exact ifComputes test (ends.andThen (FixedGadgetSubstitution.Compiler.entriesComputes endpointEncoding))
    (constantComputes e Frame.wordEncoding [])

theorem chunks_eq (rows : List RawVertex) :
    rows.flatMap (markedChunk s) =
      FixedGadgetSubstitution.Compiler.entries endpointEncoding ((rows.filter (fun row => row.1 == s)).flatMap Prod.snd) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : row.1=s
    · simp [markedChunk,h,FixedGadgetSubstitution.Compiler.entries,List.flatMap_append,ih]
    · simp [markedChunk,h,ih]

noncomputable def markedEndsComputes : Computes (inputEncoding s arity)
    (framedListEncoding endpointEncoding) (fun r => markedEnds s r.val) := by
  let rawRun := FixedGadgetSubstitution.Compiler.allRowsFlatMapComputes (s+1) 1 (extendedArity s arity) _
    (markedChunkComputes s arity)
  let run := (forgetComputes s arity).andThen rawRun
  refine recode (FixedGadgetSubstitution.Compiler.joinComputes run
    (constantComputes (inputEncoding s arity) Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro r
  change ((List.finRange r.val.vertices.length).flatMap
    (fun v => markedChunk s (r.val.vertices.get v))) ++ [false] = _
  have ha := FixedGadgetSubstitution.Compiler.all_rows (s+1) 1 (extendedArity s arity) (forget s arity r)
  change (List.finRange r.val.vertices.length).map r.val.vertices.get = r.val.vertices at ha
  rw [←List.flatMap_map,ha,chunks_eq]
  simpa only [List.append_nil,framedListEncode,framedListEncoding,markedEnds] using
    FixedGadgetSubstitution.Compiler.entries_append_encode endpointEncoding (markedEnds s r.val) []

noncomputable def firstComputes : Computes (inputEncoding s arity) endpointEncoding
    (fun r => (markedEnds s r.val).getD 0 (0,false)) :=
  (markedEndsComputes s arity).andThen (FixedGadgetSubstitution.Compiler.getDComputes endpointEncoding 0 (0,false))
noncomputable def secondComputes : Computes (inputEncoding s arity) endpointEncoding
    (fun r => (markedEnds s r.val).getD 1 (0,false)) :=
  (markedEndsComputes s arity).andThen (FixedGadgetSubstitution.Compiler.getDComputes endpointEncoding 1 (0,false))

def present (r : RawClosedNetwork) : Bool := decide (occurrences s r ≠ 0)
noncomputable def presentComputes : Computes (inputEncoding s arity) encodingBoolBool
    (fun r => present s r.val) := by
  let count := (forgetComputes s arity).andThen
    (FixedGadgetSubstitution.Compiler.occurrencesComputes (s+1) 1 (extendedArity s arity) s)
  let equal := (pairComputes count
    (constantComputes (inputEncoding s arity) UnaryBinary.unaryEncoding 0)).andThen
      (equalComputes UnaryBinary.unaryEncoding)
  let neg := FiniteRecode.computes encodingBoolBool encodingBoolBool Bool.not 1
    (fun b => by cases b <;> decide)
  exact congrComputes (equal.andThen neg) (fun r => by simp [present,forget])

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
