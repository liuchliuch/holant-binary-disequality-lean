import Holant.Proofs.Reductions.SingleWeightCompletion.Offsets
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.GraphProgram
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open ChargeProgram
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}

def componentLessComputes : Computes (probeEncoding (s:=s) (a:=a)) encodingBoolBool
    (fun p => decide (component p.1.1 p.2 < component p.1.1 p.1.2)) :=
  (pairComputes ((candidateComputes.andThen labelComputes).andThen UnaryBinary.computes)
    ((outerComputes.andThen labelComputes).andThen UnaryBinary.computes)).andThen Endpoints.lessComputes
def vertexLessComputes : Computes (probeEncoding (s:=s) (a:=a)) encodingBoolBool
    (fun p => decide (p.2.val<p.1.2.val)) :=
  (pairComputes ((candidateComputes.andThen (indexComputes s 1 a)).andThen UnaryBinary.computes)
    ((outerComputes.andThen (indexComputes s 1 a)).andThen UnaryBinary.computes)).andThen Endpoints.lessComputes
def localEarlierComputes : Computes (probeEncoding (s:=s) (a:=a)) encodingBoolBool
    (fun p => decide (component p.1.1 p.2=component p.1.1 p.1.2 ∧ p.2.val<p.1.2.val)) :=
  congrComputes (ifComputes sameComputes vertexLessComputes (constantComputes _ encodingBoolBool false))
    (fun p => by by_cases h : component p.1.1 p.2=component p.1.1 p.1.2 <;> simp [h])

def scan (w : ℕ → ℕ) (test : Probe (s:=s) (a:=a) → Bool) (x : Query s 1 a) : ℕ :=
  ((List.finRange x.1.val.vertices.length).map fun v => if test ⟨x,v⟩ then w (x.1.val.vertices.get v).1 else 0).sum
def scanComputes (w : ℕ → ℕ) (test : Probe (s:=s) (a:=a) → Bool)
    (machine : Computes (probeEncoding (s:=s) (a:=a)) encodingBoolBool test) :
    Computes (queryEncoding s 1 a) UnaryBinary.unaryEncoding (scan w test) := by
  let tokens := ifComputes machine
    ((candidateComputes.andThen (weightComputes s 1 a w)).andThen (encodeComputes UnaryBinary.unaryEncoding))
    (constantComputes _ Frame.wordEncoding [])
  let run := probesComputes.andThen (ContextFlatMap.computes (queryEncoding s 1 a)
    (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length) _ tokens)
  refine recode run id (fun _ => rfl) ?_
  intro x
  have he (v : Fin x.1.val.vertices.length) :
      (if test ⟨x,v⟩ then List.replicate (w (x.1.val.vertices.get v).1) true else []) =
        List.replicate (if test ⟨x,v⟩ then w (x.1.val.vertices.get v).1 else 0) true := by
    cases test ⟨x,v⟩ <;> rfl
  change (List.finRange _).flatMap _ = List.replicate (scan w test x) true
  dsimp only [Function.comp_def,candidate,id_eq,UnaryBinary.unaryEncoding]
  simp only [he,flatMap_tokens,scan]

variable (d : Fin s → ℕ)
def baseComputes : Computes (queryEncoding s 1 a) UnaryBinary.unaryEncoding (Offsets.base d) :=
  congrComputes (scanComputes (Offsets.weight (a:=a) d false) _ componentLessComputes)
    (fun x => by simp [scan,Offsets.base])
def prefixComputes (b : Bool) : Computes (queryEncoding s 1 a) UnaryBinary.unaryEncoding (Offsets.prefix d b) :=
  congrComputes (scanComputes (Offsets.weight (a:=a) d b) _ localEarlierComputes)
    (fun x => by simp [scan,Offsets.prefix])
def offsetComputes (b : Bool) : Computes (queryEncoding s 1 a) encodingNatBool (Offsets.edgeBase d b) :=
  (pairComputes ((pairComputes
    (((sourceComputes s 1 a).andThen (edgeCountComputes s 1 a)).andThen UnaryBinary.computes)
    ((baseComputes d).andThen UnaryBinary.computes)).andThen addComputes)
    ((prefixComputes d b).andThen UnaryBinary.computes)).andThen addComputes

def endpointComputes (b : Bool) (j : ℕ) : Computes (queryEncoding s 1 a) endpointEncoding
    (fun x => (Offsets.edgeBase d b x+j,b)) :=
  recode (pairComputes ((pairComputes (offsetComputes d b)
    (constantComputes _ encodingNatBool j)).andThen addComputes)
    (constantComputes _ encodingBoolBool b)) id (fun _ => rfl) (fun _ => rfl)
def endpointsComputes (i : Fin s) : Computes (queryEncoding s 1 a) Frame.wordEncoding
    (fun x => entries endpointEncoding ((x.1.val.vertices.get x.2).2 ++
      (List.finRange (extra (a i.val) (d i))).map
        (fun j => (Offsets.edgeBase d (pin (a i.val) (d i)) x+j.val,pin (a i.val) (d i))))) := by
  let old := (GroupingMachine.rowPortsComputes s 1 a).andThen (entriesComputes endpointEncoding)
  let fresh := fixedConcatComputes (queryEncoding s 1 a)
    (fun x (j : Fin (extra (a i.val) (d i))) => entry endpointEncoding
      (Offsets.edgeBase d (pin (a i.val) (d i)) x+j.val,pin (a i.val) (d i)))
    (fun j => (endpointComputes d (pin (a i.val) (d i)) j.val).andThen (entryComputes endpointEncoding))
    (List.finRange (extra (a i.val) (d i)))
  exact congrComputes (joinComputes old fresh) (fun _ => by simp [entries,List.flatMap_append,List.flatMap_map])

def row (x : Query s 1 a) : RawVertex :=
  let i := sourceLabel s 1 a x
  (i.val,(x.1.val.vertices.get x.2).2 ++ (List.finRange (extra (a i.val) (d i))).map
    (fun j => (Offsets.edgeBase d (pin (a i.val) (d i)) x+j.val,pin (a i.val) (d i))))
def oneRowComputes (i : Fin s) : Computes (queryEncoding s 1 a) vertexEncoding
    (fun x => (i.val,(x.1.val.vertices.get x.2).2 ++ (List.finRange (extra (a i.val) (d i))).map
      (fun j => (Offsets.edgeBase d (pin (a i.val) (d i)) x+j.val,pin (a i.val) (d i))))) := by
  let ports : Computes (queryEncoding s 1 a) (framedListEncoding endpointEncoding)
      (fun x => (x.1.val.vertices.get x.2).2 ++ (List.finRange (extra (a i.val) (d i))).map
        (fun j => (Offsets.edgeBase d (pin (a i.val) (d i)) x+j.val,pin (a i.val) (d i)))) :=
    recode (joinComputes (endpointsComputes d i) (constantComputes _ Frame.wordEncoding [false]))
      id (fun _ => rfl) (fun x => by
        change entries endpointEncoding _ ++ [false] = framedListEncode endpointEncoding _
        simpa only [List.append_nil,framedListEncode,id_eq] using entries_append_encode endpointEncoding
          ((x.1.val.vertices.get x.2).2 ++ (List.finRange (extra (a i.val) (d i))).map
            (fun j => (Offsets.edgeBase d (pin (a i.val) (d i)) x+j.val,pin (a i.val) (d i)))) [])
  exact recode (pairComputes (constantComputes _ encodingNatBool i.val) ports)
    id (fun _ => rfl) (fun _ => rfl)
def rowComputes : Computes (queryEncoding s 1 a) vertexEncoding (row d) :=
  chooseComputes (queryEncoding s 1 a) vertexEncoding s (sourceLabel s 1 a) _
    (labelRecodeComputes s 1 a UnaryBinary.unaryEncoding Fin.val) (oneRowComputes d)

def rows (r : Input (s:=s) (a:=a)) : List RawVertex := (List.finRange r.val.vertices.length).map fun v => row d ⟨r,v⟩
def rowsComputes : Computes (validatedEncoding s 1 a) (framedListEncoding vertexEncoding) (rows d) := by
  let run := allRowsFlatMapComputes s 1 a _ ((rowComputes d).andThen (entryComputes vertexEncoding))
  refine recode (joinComputes run (constantComputes _ Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro r
  change _ ++ [false] = framedListEncode vertexEncoding (rows d r)
  simpa only [rows,entries,List.flatMap_map,Function.comp_def,List.append_nil,framedListEncode,id_eq] using
    entries_append_encode vertexEncoding (rows d r) []
def edges (r : Input (s:=s) (a:=a)) : List ℕ := r.val.edges ++
  r.val.vertices.flatMap (fun v => List.replicate (Offsets.weight (a:=a) d false v.1) 0)
def edgesComputes : Computes (validatedEncoding s 1 a) (framedListEncoding encodingNatBool) (edges d) := by
  let old := (FixedGadgetSubstitution.Compiler.edgesComputes s 1 a).andThen (entriesComputes encodingNatBool)
  let fresh := allRowsFlatMapComputes s 1 a _ (labelRecodeComputes s 1 a Frame.wordEncoding
    (fun i => entries encodingNatBool (List.replicate (Offsets.weight (a:=a) d false i.val) 0)))
  refine recode (joinComputes (joinComputes old fresh) (constantComputes _ Frame.wordEncoding [false])) id
    (fun _ => rfl) ?_
  intro r
  have he := congrArg (fun rs : List RawVertex => rs.flatMap
    (fun v => entries encodingNatBool (List.replicate (Offsets.weight (a:=a) d false v.1) 0))) (all_rows s 1 a r)
  simp only [List.flatMap_map] at he
  change (entries encodingNatBool r.val.edges ++ _) ++ [false] = framedListEncode encodingNatBool (edges d r)
  simp only [sourceLabel,id_eq]
  rw [he]
  simpa only [edges,entries,List.flatMap_append,List.flatMap_assoc,List.append_nil,framedListEncode] using entries_append_encode encodingNatBool (edges d r) []
def raw (r : Input (s:=s) (a:=a)) : RawClosedNetwork := ⟨rows d r,edges d r⟩
def rawComputes : Computes (validatedEncoding s 1 a) RawClosedNetwork.encoding (raw d) :=
  recode (pairComputes (rowsComputes d) (edgesComputes d)) id (fun _ => rfl) (fun _ => rfl)

private theorem raw_ext (x y : RawClosedNetwork)
    (hv : x.vertices=y.vertices) (he : x.edges=y.edges) : x=y := by
  cases x
  cases y
  cases hv
  cases he
  rfl

theorem raw_query (r : Input (s:=s) (a:=a)) (h : Balanced d r) : raw d r = (CompletedGraph.query d r h).val := by
  apply raw_ext
  · rw [CompletedGraph.rows_exact, List.ofFn_eq_map]
    apply List.map_congr_left
    intro v _
    apply Prod.ext
    · rfl
    · change _ ++ _ = _ ++ _
      congr 1
      rw [List.ofFn_eq_map]
      apply List.map_congr_left
      intro j _
      apply Prod.ext
      · exact (Offsets.route_formula d r h ⟨v,j⟩).symm
      · rfl
  · rw [CompletedGraph.edges_exact,Offsets.total_formula]
    have hz : r.val.edges = List.replicate r.val.edges.length 0 := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        have he := r.property.2.1 ⟨i,hi⟩
        change r.val.edges[i] < 1 at he
        simpa only [List.getElem_replicate] using (show r.val.edges[i]=0 by omega)
    have flatten (vs : List RawVertex) :
        vs.flatMap (fun v => List.replicate (Offsets.weight (a:=a) d false v.1) 0) =
          List.replicate (vs.map (fun v => Offsets.weight (a:=a) d false v.1)).sum 0 := by
      induction vs with
      | nil => rfl
      | cons v vs ih => simp only [List.flatMap_cons,List.map_cons,List.sum_cons,ih,List.replicate_add]
    change r.val.edges ++ _ = _
    rw [flatten,List.replicate_add]
    exact congrArg (fun xs : List ℕ => xs ++
      List.replicate (r.val.vertices.map (fun v => Offsets.weight (a:=a) d false v.1)).sum 0) hz

end Holant.LocalDrafts.Hardness.SingleWeightCompletion.GraphProgram
