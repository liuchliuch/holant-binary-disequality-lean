import Holant.Complexity.FixedGadgetSubstitution.Compiler.Records

/-! Prefix offsets are recomputed from physically enumerated original indices.
A fixed label recoder emits one unary token per fixed template edge; concatenation
counts exactly those edges and UnaryBinary performs the real carry conversion. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev PrefixQuery := Σ x : Query s b arity, Fin x.2.val
def prefixQueryEncoding := sigmaEncoding (queryEncoding s b arity)
  (fun x => OccurrenceLabel.unaryPortEncoding x.2.val)
def earlier (x : PrefixQuery s b arity) : Query s b arity :=
  ⟨x.1.1,⟨x.2.val,Nat.lt_trans x.2.isLt x.1.2.isLt⟩⟩
noncomputable def earlierComputes : Computes (prefixQueryEncoding s b arity)
    (queryEncoding s b arity) (earlier s b arity) := by
  let source : Computes (prefixQueryEncoding s b arity) (queryEncoding s b arity) (fun x => x.1) :=
    recode (Wiring.firstComputes (queryEncoding s b arity) UnaryBinary.unaryEncoding)
      (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
  let index : Computes (prefixQueryEncoding s b arity) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
    recode (Wiring.secondComputes (queryEncoding s b arity) UnaryBinary.unaryEncoding)
      (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
  exact recode (pairComputes (source.andThen (sourceComputes s b arity)) index)
    id (fun _ => rfl) (fun _ => rfl)
def prefixQueriesEncoding := ContextFlatMap.inputEncoding (queryEncoding s b arity)
  (fun x => OccurrenceLabel.unaryPortEncoding x.2.val)
noncomputable def prefixQueriesComputes : Computes (queryEncoding s b arity)
    (prefixQueriesEncoding s b arity) (fun x => ⟨x,List.finRange x.2.val⟩) :=
  recode (pairComputes (identityComputes (queryEncoding s b arity))
    ((indexComputes s b arity).andThen ComponentSelection.UnaryRange.computes))
    id (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
      rw [←finRange_values,finListEncoding]
      rfl)
noncomputable def weightComputes (weight : ℕ → ℕ) : Computes (queryEncoding s b arity)
    UnaryBinary.unaryEncoding (fun x => weight (x.1.val.vertices.get x.2).1) :=
  labelRecodeComputes s b arity UnaryBinary.unaryEncoding (fun i => weight i.val)
def prefixWeight (weight : ℕ → ℕ) (x : Query s b arity) : ℕ :=
  ((x.1.val.vertices.take x.2.val).map (fun row => weight row.1)).sum
theorem flatMap_tokens {A : Type} (xs : List A) (f : A → ℕ) :
    xs.flatMap (fun a => List.replicate (f a) true) = List.replicate (xs.map f).sum true := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.map_cons,List.sum_cons,ih,List.replicate_add]
theorem earlier_rows (x : Query s b arity) :
    (List.finRange x.2.val).map
      (fun i => x.1.val.vertices.get ⟨i.val,Nat.lt_trans i.isLt x.2.isLt⟩) =
      x.1.val.vertices.take x.2.val := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left (Nat.le_of_lt x.2.isLt)]
  · intro i hi hj
    simp
noncomputable def prefixWeightComputes (weight : ℕ → ℕ) :
    Computes (queryEncoding s b arity) UnaryBinary.unaryEncoding (prefixWeight s b arity weight) := by
  let provider := (earlierComputes s b arity).andThen
    ((weightComputes s b arity weight).andThen (encodeComputes UnaryBinary.unaryEncoding))
  let run := (prefixQueriesComputes s b arity).andThen
    (ContextFlatMap.computes (queryEncoding s b arity)
      (fun x => OccurrenceLabel.unaryPortEncoding x.2.val) _ provider)
  refine recode run id (fun _ => rfl) (fun x => ?_)
  change (List.finRange x.2.val).flatMap
    (fun i => List.replicate (weight (x.1.val.vertices.get ⟨i.val,_⟩).1) true) =
      List.replicate (prefixWeight s b arity weight x) true
  rw [flatMap_tokens]
  apply congrArg (fun n => List.replicate n true)
  rw [prefixWeight, ←earlier_rows s b arity x, List.map_map]
  rfl
def rowOffset (templates : ℕ → Template) (x : Query s b arity) : ℕ :=
  x.1.val.edges.length + prefixWeight s b arity (fun label => (templates label).edges.length) x
noncomputable def offsetUnaryComputes (templates : ℕ → Template) :
    Computes (queryEncoding s b arity) UnaryBinary.unaryEncoding (rowOffset s b arity templates) :=
  recode (joinComputes
    (((sourceComputes s b arity).andThen (edgeCountComputes s b arity)).andThen
      (encodeComputes UnaryBinary.unaryEncoding))
    ((prefixWeightComputes s b arity (fun label => (templates label).edges.length)).andThen
      (encodeComputes UnaryBinary.unaryEncoding))) id (fun _ => rfl)
    (fun x => by simp only [Frame.wordEncoding,UnaryBinary.unaryEncoding,id_eq,rowOffset,List.replicate_add,Function.comp_def])
noncomputable def offsetComputes (templates : ℕ → Template) :
    Computes (queryEncoding s b arity) encodingNatBool (rowOffset s b arity templates) :=
  (offsetUnaryComputes s b arity templates).andThen UnaryBinary.computes
theorem all_rows (r : Input s b arity) :
    (List.finRange r.val.vertices.length).map r.val.vertices.get = r.val.vertices := by
  apply List.ext_getElem <;> simp
noncomputable def fullWeightComputes (weight : ℕ → ℕ) : Computes (validatedEncoding s b arity)
    UnaryBinary.unaryEncoding (fun r => (r.val.vertices.map (fun row => weight row.1)).sum) := by
  let run := allRowsFlatMapComputes s b arity _
    ((weightComputes s b arity weight).andThen (encodeComputes UnaryBinary.unaryEncoding))
  refine recode run id (fun _ => rfl) (fun r => ?_)
  change (List.finRange r.val.vertices.length).flatMap
    (fun i => List.replicate (weight (r.val.vertices.get i).1) true) = _
  rw [flatMap_tokens]
  change List.replicate _ true = List.replicate _ true
  apply congrArg (fun n => List.replicate n true)
  have h := congrArg (fun rows : List RawVertex => (rows.map (fun row => weight row.1)).sum)
    (all_rows s b arity r)
  simpa only [List.map_map,Function.comp_def] using h
theorem indicator_sum (label : ℕ) (rows : List RawVertex) :
    (rows.map (fun row => if row.1 = label then 1 else 0)).sum =
      (rows.filter (fun row => row.1 == label)).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : row.1 = label <;> simp [h,ih,Nat.add_comm]
noncomputable def occurrencesComputes (label : ℕ) : Computes (validatedEncoding s b arity)
    UnaryBinary.unaryEncoding (fun r => occurrences label r.val) :=
  congrComputes (fullWeightComputes s b arity (fun k => if k=label then 1 else 0))
    (fun r => indicator_sum label r.val.vertices)
end Holant.Complexity.FixedGadgetSubstitution.Compiler
