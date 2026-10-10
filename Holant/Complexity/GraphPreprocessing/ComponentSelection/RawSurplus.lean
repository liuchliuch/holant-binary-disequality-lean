import Holant.Complexity.GraphPreprocessing.ComponentSelection.SurplusList
import Holant.Complexity.GraphPreprocessing.ComponentSelection.UnaryRange
import Holant.Complexity.GraphPreprocessing.ComponentSelection.ClassifyList

/-! Original raw graph and original vertex to an exact component-surplus
classification. The raw edge and parent tables, least component root and full
original edge-ID list are produced by finite machines within this execution. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.RawSurplus
open Turing Computability BinaryCompose FixedFieldMachines OriginalCoefficient
open Holant.OneHot.Computable Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
abbrev Input := RawRootReach.Input
abbrev inputEncoding := RawRootReach.inputEncoding
noncomputable def sourceComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (RawClosedNetwork.validatedEncoding s b arity) (fun x => x.1) :=
  recode (Wiring.firstComputes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding)
    (fun x => (x.1,List.replicate x.2.val true)) (fun _ => rfl) (fun _ => rfl)
def context (x : Input s b arity) :=
  EndpointPredicate.originalContext (x.1.val.graph x.1.property) ((x.1.val.graph x.1.property).label x.2)
noncomputable def contextComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) EndpointPredicate.contextEncoding context :=
  recode (pairComputes ((sourceComputes s b arity).andThen (RawChildren.contextComputes s b arity))
    (RawComponentLabel.computes s b arity)) id (fun _ => rfl) (fun _ => rfl)
noncomputable def countsComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity)
      (pairEncoding (RawClosedNetwork.validatedEncoding s b arity)
        (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
      (fun x => (x,(x.val.vertices.length,x.val.edges.length))) :=
  recode (RawEdgeTable.countsComputes s b arity) id (fun _ => rfl) (fun _ => rfl)
noncomputable def edgeCountComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) UnaryBinary.unaryEncoding (fun x => x.1.val.edges.length) :=
  (((sourceComputes s b arity).andThen (countsComputes s b arity)).andThen
    (Wiring.secondComputes (RawClosedNetwork.validatedEncoding s b arity)
      (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))).andThen
    (Wiring.secondComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
noncomputable def indicesComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (framedListEncoding UnaryBinary.unaryEncoding)
      (fun x => List.range x.1.val.edges.length) :=
  (edgeCountComputes s b arity).andThen UnaryRange.computes
def prepared (x : Input s b arity) : SurplusList.Input :=
  SurplusList.original (x.1.val.graph x.1.property) ((x.1.val.graph x.1.property).label x.2)
theorem index_encoding (n : ℕ) (xs : List (Fin n)) :
    framedListEncode UnaryBinary.unaryEncoding (xs.map Fin.val)=
      framedListEncode (OccurrenceLabel.unaryPortEncoding n) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,framedListEncode,ih]; rfl
theorem range_values (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem <;> simp
noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) SurplusList.inputEncoding prepared :=
  recode (pairComputes (contextComputes s b arity) (indicesComputes s b arity)) id (fun _ => rfl)
    (fun x => by
      change Holant.Algebraic.frame (EndpointPredicate.contextEncoding.encode (context x))++
        framedListEncode UnaryBinary.unaryEncoding (List.range x.1.val.edges.length)=
        Holant.Algebraic.frame (EndpointPredicate.contextEncoding.encode (context x))++
        framedListEncode (OccurrenceLabel.unaryPortEncoding (ReachRound.graphEdges (x.1.val.graph x.1.property)).length)
          (List.finRange (ReachRound.graphEdges (x.1.val.graph x.1.property)).length)
      rw [←index_encoding,range_values]
      simp only [ReachRound.graphEdges,List.length_map,RawClosedNetwork.graph_edges])
def edges (x : Input s b arity) : List ℕ :=
  (surplusEdges (x.1.val.graph x.1.property) ((x.1.val.graph x.1.property).label x.2)).map Fin.val
noncomputable def edgesComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) SurplusList.outputEncoding edges :=
  congrComputes ((prepareComputes s b arity).andThen SurplusList.computes)
    (fun x => SurplusList.original_value (x.1.val.graph x.1.property) ((x.1.val.graph x.1.property).label x.2))
def value (x : Input s b arity) : Classification := classify (edges x)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) ClassifyList.outputEncoding value :=
  (edgesComputes s b arity).andThen ClassifyList.computes
abbrev contextMachine : Machine := pairMachine (Wiring.firstMachine.compose RawChildren.contextMachine) RawComponentLabel.machine
abbrev edgeCountMachine : Machine := ((Wiring.firstMachine.compose CountsPackage.machine).compose secondMachine).compose secondMachine
abbrev indicesMachine : Machine := edgeCountMachine.compose UnaryRange.machine
abbrev prepareMachine : Machine := pairMachine contextMachine indicesMachine
abbrev edgesMachine : Machine := prepareMachine.compose SurplusList.machine
abbrev machine : Machine := edgesMachine.compose ClassifyList.machine
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine := rfl
theorem inFP : InFP (inputEncoding s b arity) ClassifyList.outputEncoding value := (computes s b arity).inFP
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (computes s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x)
      (some (ClassifyList.outputEncoding.encode (value x)))
      ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := ((computes s b arity).outputs x).steps
  evals_in_steps := ((computes s b arity).outputs x).evals_in_steps
  steps_le_m := le_trans ((computes s b arity).outputs x).steps_le_m
    (by simpa [timePolynomial] using (natPolynomial_eval_mono (computes s b arity).time
      (RawRootReach.input_length_le_original x)))
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost machine (timed x).steps (some (initList machine.computer ((inputEncoding s b arity).encode x)))≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
theorem unicycle_unused (x : Input s b arity) (e : ℕ) (h : value x=.unicycle e) :
    ∃ q : Fin x.1.val.edges.length, q.val=e ∧
      ∀ v : Fin x.1.val.vertices.length, ∀p∈((x.1.val.graph x.1.property).parentRow v).parent,p.1≠q.val := by
  obtain ⟨q,hq,hu,_⟩ := ComponentSelection.unicycle_unused (x.1.val.graph x.1.property)
    ((x.1.val.graph x.1.property).label x.2) e h
  exact ⟨Fin.cast (x.1.val.graph_edges x.1.property) q,hq,hu⟩
end Holant.Complexity.GraphPreprocessing.ComponentSelection.RawSurplus
