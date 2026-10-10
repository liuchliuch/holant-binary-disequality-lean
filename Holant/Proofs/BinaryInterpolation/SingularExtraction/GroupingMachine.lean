import Holant.Proofs.BinaryInterpolation.SingularExtraction.UnaryQuotient
import Holant.Proofs.BinaryInterpolation.SingularExtraction.RawGrouping


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.GroupingMachine
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
variable (s b : ℕ) (arity : ℕ → ℕ) (label k : ℕ) (hk : 0 < k)

def rowPortsComputes : Computes (queryEncoding s b arity) (framedListEncoding endpointEncoding)
    (fun x => (x.1.val.vertices.get x.2).2) :=
  (originalRowComputes s b arity).andThen
    (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))

def selectedChunk (x : Query s b arity) : List Bool :=
  if (x.1.val.vertices.get x.2).1 = label then entries endpointEncoding (x.1.val.vertices.get x.2).2 else []

def selectedChunkComputes : Computes (queryEncoding s b arity) Frame.wordEncoding
    (selectedChunk s b arity label) :=
  chooseComputes (queryEncoding s b arity) Frame.wordEncoding s (sourceLabel s b arity)
    (fun x i => if i.val=label then entries endpointEncoding (x.1.val.vertices.get x.2).2 else [])
    (labelRecodeComputes s b arity UnaryBinary.unaryEncoding Fin.val)
    (fun i => if h : i.val=label then by
      simp only [h, if_true]
      exact (rowPortsComputes s b arity).andThen (entriesComputes endpointEncoding)
    else by simpa only [h, if_false] using constantComputes (queryEncoding s b arity) Frame.wordEncoding [])

theorem selected_word (rows : List RawVertex) :
    rows.flatMap (fun row => if row.1=label then entries endpointEncoding row.2 else []) =
      entries endpointEncoding (RawGrouping.selected label rows) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    unfold entries RawGrouping.selected at ih ⊢
    by_cases h : row.1=label <;> simp [h, ih, List.flatMap_append]

def selectedComputes : Computes (validatedEncoding s b arity) (framedListEncoding endpointEncoding)
    (fun r => RawGrouping.selected label r.val.vertices) := by
  let run := allRowsFlatMapComputes s b arity _ (selectedChunkComputes s b arity label)
  refine recode (joinComputes run (constantComputes _ Frame.wordEncoding [false])) id
    (fun _ => rfl) (fun r => ?_)
  have h := congrArg (fun rows : List RawVertex => rows.flatMap
    (fun row => if row.1=label then entries endpointEncoding row.2 else [])) (all_rows s b arity r)
  simp only [List.flatMap_map] at h
  dsimp only [id_eq]
  change _ ++ [false] = _
  rw [show (List.finRange r.val.vertices.length).flatMap
      (fun i => selectedChunk s b arity label ⟨r,i⟩) =
      entries endpointEncoding (RawGrouping.selected label r.val.vertices) from
    h.trans (selected_word label r.val.vertices)]
  simpa only [framedListEncoding, framedListEncode, List.append_nil] using entries_append_encode endpointEncoding (RawGrouping.selected label r.val.vertices) []

def keptChunk (x : Query s b arity) : List Bool :=
  if (x.1.val.vertices.get x.2).1 = label then [] else entry vertexEncoding (x.1.val.vertices.get x.2)

def keptChunkComputes : Computes (queryEncoding s b arity) Frame.wordEncoding (keptChunk s b arity label) :=
  chooseComputes (queryEncoding s b arity) Frame.wordEncoding s (sourceLabel s b arity)
    (fun x i => if i.val=label then [] else entry vertexEncoding (x.1.val.vertices.get x.2))
    (labelRecodeComputes s b arity UnaryBinary.unaryEncoding Fin.val)
    (fun i => if h : i.val=label then by
      simpa only [h, if_true] using constantComputes (queryEncoding s b arity) Frame.wordEncoding []
    else by
      simp only [h, if_false]
      exact (originalRowComputes s b arity).andThen (entryComputes vertexEncoding))

theorem kept_word (rows : List RawVertex) :
    rows.flatMap (fun row => if row.1=label then [] else entry vertexEncoding row) =
      entries vertexEncoding (RawGrouping.keep label rows) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => by_cases h : row.1=label <;> simp [RawGrouping.keep, entries, h, ih]

def keptEntriesComputes : Computes (validatedEncoding s b arity) Frame.wordEncoding
    (fun r => entries vertexEncoding (RawGrouping.keep label r.val.vertices)) := by
  refine congrComputes (allRowsFlatMapComputes s b arity _ (keptChunkComputes s b arity label)) ?_
  intro r
  have h := congrArg (fun rows : List RawVertex => rows.flatMap
    (fun row => if row.1=label then [] else entry vertexEncoding row)) (all_rows s b arity r)
  simp only [List.flatMap_map] at h
  exact h.trans (kept_word label r.val.vertices)

variable (ha : arity label = 1)

include ha in
theorem selected_length (r : Input s b arity) :
    (RawGrouping.selected label r.val.vertices).length = occurrences label r.val := by
  apply RawGrouping.selected_length
  intro row hr he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  have hw := (r.property.1 i).2
  change (r.val.vertices.get i).2.length = arity (r.val.vertices.get i).1 at hw
  rw [he, ha] at hw
  exact hw

def blockCount (r : Input s b arity) : ℕ := occurrences label r.val / k
abbrev BlockQuery := Σ r : Input s b arity, Fin (blockCount s b arity label k r)
def blockEncoding := sigmaEncoding (validatedEncoding s b arity)
  (fun r => OccurrenceLabel.unaryPortEncoding (blockCount s b arity label k r))

def blockSourceComputes : Computes (blockEncoding s b arity label k) (validatedEncoding s b arity)
    (fun x => x.1) :=
  recode (Wiring.firstComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def blockIndexComputes : Computes (blockEncoding s b arity label k) UnaryBinary.unaryEncoding
    (fun x => x.2.val) :=
  recode (Wiring.secondComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def endpointIndex (ha : arity label = 1) (x : BlockQuery s b arity label k) (j : Fin k) :
    Fin (RawGrouping.selected label x.1.val.vertices).length :=
  ⟨k*x.2.val+j.val, by
    rw [selected_length s b arity label ha]
    have hi := x.2.isLt
    have hj := j.isLt
    have hq := Nat.div_mul_le_self (occurrences label x.1.val) k
    have hm := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hi)
    dsimp [blockCount] at hm
    nlinarith⟩

def endpointComputes (j : Fin k) : Computes (blockEncoding s b arity label k) endpointEncoding
    (fun x => (RawGrouping.selected label x.1.val.vertices).get (endpointIndex s b arity label k ha x j)) := by
  let ix := ((blockIndexComputes s b arity label k).andThen (UnaryQuotient.timesComputes k)).andThen
    (UnaryQuotient.addConstantComputes j.val)
  let pre : Computes (blockEncoding s b arity label k) (ParentRowSelect.inputEncoding endpointEncoding)
      (fun x => ⟨RawGrouping.selected label x.1.val.vertices,endpointIndex s b arity label k ha x j⟩) :=
    recode (pairComputes ((blockSourceComputes s b arity label k).andThen
      (selectedComputes s b arity label)) ix) id (fun _ => rfl) (fun _ => rfl)
  exact pre.andThen (ParentRowSelect.computes endpointEncoding)

def blockRow (x : BlockQuery s b arity label k) : RawVertex :=
  (label,(List.finRange k).map fun j =>
    (RawGrouping.selected label x.1.val.vertices).get (endpointIndex s b arity label k ha x j))

def blockRowComputes : Computes (blockEncoding s b arity label k) vertexEncoding
    (blockRow s b arity label k ha) :=
  recode (pairComputes (constantComputes _ encodingNatBool label)
    (fixedListComputes (blockEncoding s b arity label k) endpointEncoding
      (fun x j => (RawGrouping.selected label x.1.val.vertices).get (endpointIndex s b arity label k ha x j))
      (endpointComputes s b arity label k ha) (List.finRange k))) id (fun _ => rfl) (fun _ => rfl)

theorem blocks_indexed (ps : List RawEndpoint) (q : ℕ) :
    RawGrouping.blocks label k q ps =
      (List.range q).map (fun i => (label,(ps.drop (k*i)).take k)) := by
  induction q generalizing ps with
  | zero => rfl
  | succ q ih =>
    simp [RawGrouping.blocks, List.range_succ_eq_map, ih, List.map_map,
      Function.comp_def, List.drop_drop, Nat.mul_add, Nat.add_comm]

theorem blockRow_ports (x : BlockQuery s b arity label k) :
    (blockRow s b arity label k ha x).2 =
      ((RawGrouping.selected label x.1.val.vertices).drop (k*x.2.val)).take k := by
  have hq := Nat.div_mul_le_self (occurrences label x.1.val) k
  have hm := Nat.mul_le_mul_right k (Nat.succ_le_of_lt x.2.isLt)
  have hs := selected_length s b arity label ha x.1
  dsimp [blockCount] at hm
  rw [Nat.succ_mul, Nat.mul_comm x.2.val k] at hm
  apply List.ext_getElem
  · simp [blockRow, List.length_take, List.length_drop]
    rw [hs]
    omega
  · intro i hi hj
    simp [blockRow, endpointIndex, List.get_eq_getElem, Nat.add_comm]

theorem blockRows_eq (r : Input s b arity) :
    (List.finRange (blockCount s b arity label k r)).map
      (fun i => blockRow s b arity label k ha ⟨r,i⟩) =
      RawGrouping.blocks label k ((RawGrouping.selected label r.val.vertices).length/k)
        (RawGrouping.selected label r.val.vertices) := by
  rw [blocks_indexed label k, selected_length s b arity label ha]
  apply List.ext_getElem
  · simp [blockCount]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    refine Prod.ext (by rfl) ?_
    exact blockRow_ports s b arity label k ha _

def blockEntriesComputes (hk : 0 < k) (ha : arity label = 1) : Computes (validatedEncoding s b arity) Frame.wordEncoding
    (fun r => entries vertexEncoding
      (RawGrouping.blocks label k ((RawGrouping.selected label r.val.vertices).length/k)
        (RawGrouping.selected label r.val.vertices))) := by
  let pre : Computes (validatedEncoding s b arity)
      (ContextFlatMap.inputEncoding (validatedEncoding s b arity)
        (fun r => OccurrenceLabel.unaryPortEncoding (blockCount s b arity label k r)))
      (fun r => ⟨r,List.finRange (blockCount s b arity label k r)⟩) :=
    recode (pairComputes (identityComputes _)
      (((occurrencesComputes s b arity label).andThen (UnaryQuotient.computes k hk)).andThen
        ComponentSelection.UnaryRange.computes)) id (fun _ => rfl) (fun r => by
          change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
          rw [← finRange_values, finListEncoding]; rfl)
  let run := pre.andThen (ContextFlatMap.computes (validatedEncoding s b arity)
    (fun r => OccurrenceLabel.unaryPortEncoding (blockCount s b arity label k r)) _
    ((blockRowComputes s b arity label k ha).andThen (entryComputes vertexEncoding)))
  refine congrComputes run ?_
  intro r
  have h := congrArg (entries vertexEncoding) (blockRows_eq s b arity label k ha r)
  simp only [entries, List.flatMap_map] at h
  exact h

def rowsComputes (hk : 0 < k) (ha : arity label = 1) : Computes (validatedEncoding s b arity) (framedListEncoding vertexEncoding)
    (fun r => (RawGrouping.groupOne label k r.val).vertices) :=
  recode (joinComputes (joinComputes (keptEntriesComputes s b arity label)
    (blockEntriesComputes s b arity label k hk ha)) (constantComputes _ Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun r => by
      simpa [entries, List.flatMap_append, List.append_assoc, RawGrouping.groupOne, Frame.wordEncoding, framedListEncoding, framedListEncode] using
        entries_append_encode vertexEncoding (RawGrouping.groupOne label k r.val).vertices [])

/-- Actual raw grouping compiler. Divisibility is needed for output validation,
not for totality or execution of this finite program. -/
def computes : Computes (validatedEncoding s b arity) encoding
    (fun r => RawGrouping.groupOne label k r.val) :=
  recode (pairComputes (rowsComputes s b arity label k hk ha) (Compiler.edgesComputes s b arity))
    id (fun _ => rfl) (fun _ => rfl)

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.GroupingMachine
