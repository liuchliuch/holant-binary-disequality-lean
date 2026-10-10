import Holant.Proofs.LinearProgramming.RawSource
import Holant.Proofs.Tractability.EOEvaluation.MatrixRefinement
import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Responses
import Holant.Proofs.Algorithms.OptionalValue


namespace Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOCommonPointSource
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines StackProtocol GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.Tractability
open Holant.LocalDrafts.Tractability.EOEvaluation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

/-- Original physical addresses, including the literal original vertex row. -/
abbrev WeightedColumn := RawColumns.Column × ℚ
def weightedColumnEncoding := pairEncoding RawColumns.columnEncoding rationalEncoding
def weightTableEncoding := framedListEncoding weightedColumnEncoding
def maskEncoding := framedListEncoding encodingBoolBool
/-- The original point is retained along with its addressed weights and mask. -/
abbrev Payload := List ℚ × (List WeightedColumn × List Bool)
def payloadEncoding := pairEncoding Codec.pointEncoding
  (pairEncoding weightTableEncoding maskEncoding)
abbrev Result := Option (Option Payload)
def outputEncoding := optionEncoding (optionEncoding payloadEncoding)

def defaultColumn : RawColumns.Column := (0,(0,[]),0)
def weightTable (r : EOEvaluation.Source.Input (s := s) (arity := arity)) (xs : List ℚ) : List WeightedColumn :=
  (List.range (RawColumns.columns r).length).map
    (fun j => ((RawColumns.columns r).getD j defaultColumn,xs.getD j 0))
def mask (xs : List ℚ) : List Bool := xs.map (fun q => decide (0<q))
def payload (r : EOEvaluation.Source.Input (s := s) (arity := arity)) (xs : List ℚ) : Payload :=
  (xs,(weightTable r xs,mask xs))
def weights (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (xs : List ℚ) : Relaxation.Weights (EOEvaluation.Source.network D r) :=
  MatrixRefinement.weights D r (Codec.point (MatrixCompiler.raw D r) xs)

/-- This is the same actual strict parser/point machine on equal legal bytes.
The additional outer Some is its actual return, not an extra instruction. -/
private def uniformPoint : Computes Codec.inputEncoding RawSource.outputEncoding
    (fun d => some (CommonSupportPoint.value d)) :=
  recode RawSource.entry Codec.inputEncoding.encode (fun _ => rfl)
    (fun d => congrArg RawSource.outputEncoding.encode
      (RawSource.legal_value d))
private def pointComputes (D : EOEvaluation.Source.Family s arity) :
    Computes EOEvaluation.Source.inputEncoding RawSource.outputEncoding
      (fun r => some (CommonSupportPoint.value (MatrixCompiler.value D r))) :=
  (MatrixCompiler.computes D).andThen uniformPoint

private abbrev Context (s : ℕ) (arity : ℕ → ℕ) :=
  EOEvaluation.Source.Input (s := s) (arity := arity) × Option (Option (List ℚ))
private def contextEncoding := pairEncoding
  (EOEvaluation.Source.inputEncoding (s := s) (arity := arity)) RawSource.outputEncoding
private def sourcePrepare (D : EOEvaluation.Source.Family s arity) :
    Computes EOEvaluation.Source.inputEncoding contextEncoding
      (fun r => (r,some (CommonSupportPoint.value (MatrixCompiler.value D r)))) :=
  pairComputes (identityComputes EOEvaluation.Source.inputEncoding) (pointComputes D)
private def original : Computes contextEncoding EOEvaluation.Source.inputEncoding
    (fun c : Context s arity => c.1) := Wiring.firstComputes _ _
private def returned : Computes contextEncoding RawSource.outputEncoding
    (fun c : Context s arity => c.2) := Wiring.secondComputes _ _
private def innerReturned : Computes contextEncoding Codec.outputEncoding
    (fun c : Context s arity => c.2.getD none) :=
  returned.andThen (Holant.LocalDrafts.MainChain.OptionalValue.getDComputes Codec.outputEncoding none)
private def actualPoint : Computes contextEncoding Codec.pointEncoding
    (fun c : Context s arity => (c.2.getD none).getD []) :=
  innerReturned.andThen (Holant.LocalDrafts.MainChain.OptionalValue.getDComputes Codec.pointEncoding [])

private abbrev Saved (s : ℕ) (arity : ℕ → ℕ) := Context s arity × List RawColumns.Column
private def savedEncoding := pairEncoding (contextEncoding (s := s) (arity := arity)) RawColumns.columnsEncoding
private def save : Computes contextEncoding savedEncoding
    (fun c : Context s arity => (c,RawColumns.columns c.1)) :=
  pairComputes (identityComputes contextEncoding) (original.andThen RawColumns.computes)
private def savedContext : Computes savedEncoding contextEncoding
    (fun c : Saved s arity => c.1) := Wiring.firstComputes _ _
private def savedColumns : Computes savedEncoding RawColumns.columnsEncoding
    (fun c : Saved s arity => c.2) := Wiring.secondComputes _ _
private def savedPoint := (savedContext (s := s) (arity := arity)).andThen actualPoint
private def count := (savedColumns (s := s) (arity := arity)).andThen
  (WireLists.lengthComputes RawColumns.columnEncoding)
private def indexedEncoding := pairEncoding (savedEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
private def weightCell : Computes indexedEncoding weightedColumnEncoding
    (fun q : Saved s arity × ℕ =>
      (q.1.2.getD q.2 defaultColumn,((q.1.1.2.getD none).getD []).getD q.2 0)) := by
  let ctx := Wiring.firstComputes (savedEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes (savedEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  exact pairComputes (AccessPrograms.get RawColumns.columnEncoding defaultColumn
    (ctx.andThen savedColumns) j) (AccessPrograms.get rationalEncoding 0 (ctx.andThen savedPoint) j)
private def tableComputes : Computes savedEncoding weightTableEncoding
    (fun c : Saved s arity => (List.range c.2.length).map
      (fun j => (c.2.getD j defaultColumn,((c.1.2.getD none).getD []).getD j 0))) :=
  WireLists.tabulate savedEncoding weightedColumnEncoding (fun c : Saved s arity => c.2.length)
    count (fun c j => (c.2.getD j defaultColumn,((c.1.2.getD none).getD []).getD j 0)) weightCell
private def maskComputes : Computes Codec.pointEncoding maskEncoding mask :=
  WireLists.mapComputes rationalEncoding encodingBoolBool (fun q => decide (0<q)) Foundation.Comparison.rationalPositive
private def payloadComputes : Computes savedEncoding payloadEncoding
    (fun c : Saved s arity =>
      (((c.1.2.getD none).getD []),
        ((List.range c.2.length).map (fun j =>
          (c.2.getD j defaultColumn,((c.1.2.getD none).getD []).getD j 0)),
          mask ((c.1.2.getD none).getD [])))) :=
  pairComputes savedPoint (pairComputes tableComputes (savedPoint.andThen maskComputes))

private def presence {A : Type} (ea : Encoding A Bool) :
    Computes (optionEncoding ea) encodingBoolBool Option.isSome :=
  congrComputes ((OptionMap.computes (constantComputes ea encodingBoolBool true)).andThen OptionAny.computes)
    (fun q => by cases q <;> rfl)
private def someComputes {A : Type} (ea : Encoding A Bool) :
    Computes ea (optionEncoding ea) (fun x => some x) :=
  recode (joinComputes (constantComputes ea Frame.wordEncoding [true]) (encodeComputes ea))
    id (fun _ => rfl) (fun _ => rfl)
private def finishValue (c : Saved s arity) : Result :=
  if c.1.2.isSome then
    if (c.1.2.getD none).isSome then
      some (some (((c.1.2.getD none).getD []),
        ((List.range c.2.length).map (fun j =>
          (c.2.getD j defaultColumn,((c.1.2.getD none).getD []).getD j 0)),
          mask ((c.1.2.getD none).getD []))))
    else some none
  else none
private def finish : Computes (savedEncoding (s := s) (arity := arity)) outputEncoding
    (finishValue (s := s) (arity := arity)) :=
  ifComputes ((savedContext.andThen returned).andThen (presence Codec.outputEncoding))
    (ifComputes ((savedContext.andThen innerReturned).andThen (presence Codec.pointEncoding))
      (payloadComputes.andThen ((someComputes payloadEncoding).andThen
        (someComputes (optionEncoding payloadEncoding))))
      (constantComputes savedEncoding outputEncoding (some none)))
    (constantComputes savedEncoding outputEncoding none)

def value (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity)) : Result :=
  some ((CommonSupportPoint.value (MatrixCompiler.value D r)).map (payload r))
private def nativeComputes (D : EOEvaluation.Source.Family s arity) : Computes EOEvaluation.Source.inputEncoding outputEncoding
    (fun r => finishValue ((r,some (CommonSupportPoint.value (MatrixCompiler.value D r))),RawColumns.columns r)) :=
  (sourcePrepare D).andThen (save.andThen finish)
private theorem native_exact (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity)) :
    finishValue ((r,some (CommonSupportPoint.value (MatrixCompiler.value D r))),RawColumns.columns r)=value D r := by
  cases he : CommonSupportPoint.value (MatrixCompiler.value D r) <;>
    simp only [finishValue,value,he,Option.isSome_some,Option.isSome_none,Option.getD_some,
      Option.getD_none,Option.map_some,Option.map_none,Bool.false_eq_true,↓reduceIte,payload,weightTable]

theorem mask_at (xs : List ℚ) (j : ℕ) : (mask xs).getD j false=decide (0<xs.getD j 0) := by
  simpa only [mask,show decide ((0 : ℚ)<0)=false from rfl] using
    (List.getD_map (l := xs) (d := (0 : ℚ)) (n := j) (fun q => decide (0<q)))

theorem weightTable_length (r : EOEvaluation.Source.Input (s := s) (arity := arity)) (xs : List ℚ) :
    (weightTable r xs).length=(RawColumns.columns r).length := by simp [weightTable]
theorem weightTable_at (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (xs : List ℚ) (j : Fin (MatrixCompiler.raw D r).dimension) :
    (weightTable r xs).getD j.val (defaultColumn,0)=
      (ColumnOrder.encode r (ColumnOrder.order r j),
        weights D r xs (ColumnOrder.order r j).1 (ColumnOrder.order r j).2) := by
  have hj : j.val < (RawColumns.columns r).length := j.isLt
  have ht : j.val < (weightTable r xs).length := by simpa only [weightTable_length] using hj
  rw [List.getD_eq_getElem _ _ ht]
  simp only [weightTable,List.getElem_map,List.getElem_range]
  have hcol : (RawColumns.columns r).getD j.val defaultColumn=
      ColumnOrder.encode r (ColumnOrder.order r j) := by
    rw [List.getD_eq_get _ _ ⟨j.val, hj⟩]
    exact ColumnOrder.get_order r ⟨j.val, hj⟩
  rw [hcol]
  congr 1
  change xs.getD j.val 0 = xs.getD ((ColumnOrder.order r).symm ((ColumnOrder.order r) j)).val 0
  rw [(ColumnOrder.order r).symm_apply_apply]

private theorem unpack (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (y : Payload) (hy : value D r=some (some y)) :
    CommonSupportPoint.value (MatrixCompiler.value D r)=some y.1 ∧ y=payload r y.1 := by
  have hm := Option.some.inj hy
  obtain ⟨xs,hx,hp⟩ := Option.map_eq_some_iff.mp hm
  have hfirst : xs=y.1 := congrArg Prod.fst hp
  subst xs
  exact ⟨hx,hp.symm⟩

theorem addressed_output (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (y : Payload) (hy : value D r=some (some y)) :
    y=payload r y.1 ∧
      y.2.1.length=(MatrixCompiler.raw D r).dimension ∧
      (∀ j : Fin (MatrixCompiler.raw D r).dimension,
        y.2.1.getD j.val (defaultColumn,0)=
          (ColumnOrder.encode r (ColumnOrder.order r j),
            weights D r y.1 (ColumnOrder.order r j).1 (ColumnOrder.order r j).2)) := by
  have he := (unpack D r y hy).2
  have ht : y.2.1=weightTable r y.1 := congrArg (fun z : Payload => z.2.1) he
  refine ⟨he,?_,?_⟩
  · rw [ht,weightTable_length]
    rfl
  · intro j
    rw [ht]
    exact weightTable_at D r y.1 j

theorem common_sound (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (y : Payload) (hy : value D r=some (some y)) :
    Codec.Solution (MatrixCompiler.raw D r) y.1 ∧
      Relaxation.Feasible (EOEvaluation.Source.network D r) (weights D r y.1) ∧
      (∀ c : EOEvaluation.Source.Coordinate r,
        0<weights D r y.1 c.1 c.2 ↔ Relaxation.Candidate (EOEvaluation.Source.network D r) c.1 c.2) ∧
      (∀ c : EOEvaluation.Source.Coordinate r,
        weights D r y.1 c.1 c.2=0 ↔ ¬Relaxation.Candidate (EOEvaluation.Source.network D r) c.1 c.2) := by
  obtain ⟨hx,_⟩ := unpack D r y hy
  obtain ⟨hs,hp,hz⟩ := CommonSupportProgram.Source.support (MatrixCompiler.value D r) y.1 hx
  refine ⟨hs,(MatrixRefinement.feasible_iff D r _).mp hs.2,?_,?_⟩
  · intro c
    let j := (ColumnOrder.order r).symm c
    have h := (hp j).trans (MatrixRefinement.positive_iff D r j)
    have he : Relaxation.Candidate (EOEvaluation.Source.network D r)
        ((ColumnOrder.order r) j).1 ((ColumnOrder.order r) j).2 ↔
          Relaxation.Candidate (EOEvaluation.Source.network D r) c.1 c.2 :=
      Iff.of_eq (congrArg (fun z : EOEvaluation.Source.Coordinate r =>
        Relaxation.Candidate (EOEvaluation.Source.network D r) z.1 z.2)
          ((ColumnOrder.order r).apply_symm_apply c))
    simpa only [weights,MatrixRefinement.weights,MatrixCompiler.value,j,Sigma.eta] using h.trans he
  · intro c
    let j := (ColumnOrder.order r).symm c
    have h := (hz j).trans (not_congr (MatrixRefinement.positive_iff D r j))
    have he : Relaxation.Candidate (EOEvaluation.Source.network D r)
        ((ColumnOrder.order r) j).1 ((ColumnOrder.order r) j).2 ↔
          Relaxation.Candidate (EOEvaluation.Source.network D r) c.1 c.2 :=
      Iff.of_eq (congrArg (fun z : EOEvaluation.Source.Coordinate r =>
        Relaxation.Candidate (EOEvaluation.Source.network D r) z.1 z.2)
          ((ColumnOrder.order r).apply_symm_apply c))
    simpa only [weights,MatrixRefinement.weights,MatrixCompiler.value,j,Sigma.eta] using h.trans (not_congr he)

/-- The physically returned positivity mask is the existing candidate specification;
the old LP candidate machine is not called or identified with this machine. -/
theorem mask_original (D : EOEvaluation.Source.Family s arity)
    (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (y : Payload) (hy : value D r=some (some y)) :
    y.2.2=CandidateExecution.Responses.truth D r := by
  obtain ⟨hx,he⟩ := unpack D r y hy
  obtain ⟨hs,hp,_⟩ := CommonSupportProgram.Source.support (MatrixCompiler.value D r) y.1 hx
  have hmask : y.2.2=mask y.1 := congrArg (fun z : Payload => z.2.2) he
  rw [hmask]
  apply List.ext_getElem
  · simpa only [mask,List.length_map,CandidateExecution.Responses.truth,List.length_ofFn,
      MatrixCompiler.value] using hs.1
  · intro i hi ht
    let j : Fin (MatrixCompiler.raw D r).dimension := ⟨i,by
      simpa only [mask,List.length_map,hs.1,MatrixCompiler.value] using hi⟩
    have heq : (mask y.1).getD i false=
        (CandidateExecution.Responses.truth D r).getD i false := by
      apply Bool.eq_iff_iff.mpr
      rw [mask_at,decide_eq_true_eq]
      exact (hp j).trans (CandidateExecution.Responses.truth_at D r j).symm
    simpa only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ ht] using heq

theorem zero_dimension_success (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (hn : (MatrixCompiler.raw D r).dimension=0) (y : Payload) (hy : value D r=some (some y)) :
    y.1=[] ∧ y.2.1=[] ∧ y.2.2=[] := by
  have hs := (common_sound D r y hy).1.1
  have hx : y.1=[] := List.eq_nil_iff_length_eq_zero.mpr (hs.trans hn)
  have ha := addressed_output D r y hy
  have ht : y.2.1=[] := List.eq_nil_iff_length_eq_zero.mpr (ha.2.1.trans hn)
  have hm : y.2.2=mask y.1 := congrArg (fun z : Payload => z.2.2) ha.1
  refine ⟨hx,ht,?_⟩
  rw [hm,hx]
  rfl

theorem not_malformed (D : EOEvaluation.Source.Family s arity) (r : EOEvaluation.Source.Input (s := s) (arity := arity)) :
    value D r≠none := by
  change some ((CommonSupportPoint.value (MatrixCompiler.value D r)).map (payload r))≠none
  intro h
  cases h
theorem feasible_original_iff (D : EOEvaluation.Source.Family s arity)
    (r : EOEvaluation.Source.Input (s := s) (arity := arity)) :
    (∃ x, Codec.Feasible (MatrixCompiler.raw D r) x) ↔
      ∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨MatrixRefinement.weights D r x,(MatrixRefinement.feasible_iff D r x).mp hx⟩
  · rintro ⟨w,hw⟩
    refine ⟨MatrixRefinement.point D r w,(MatrixRefinement.feasible_iff D r _).mpr ?_⟩
    simpa only [MatrixRefinement.weights_point] using hw

theorem infeasible_original_iff (D : EOEvaluation.Source.Family s arity)
    (r : EOEvaluation.Source.Input (s := s) (arity := arity)) :
    value D r=some none ↔ ¬∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w := by
  rw [value,Option.some.injEq,Option.map_eq_none_iff]
  exact (CommonSupportPoint.none_iff (MatrixCompiler.value D r)).trans
    (not_congr (feasible_original_iff D r))

theorem complete (D : EOEvaluation.Source.Family s arity)
    (r : EOEvaluation.Source.Input (s := s) (arity := arity))
    (hf : ∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w) :
    ∃ y, value D r=some (some y) := by
  obtain ⟨xs,hx,_⟩ := CommonSupportPoint.complete (MatrixCompiler.value D r)
    ((feasible_original_iff D r).mpr hf)
  exact ⟨payload r xs,by rw [value,hx,Option.map_some]⟩

namespace Source
variable (D : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Family s arity)
def computes : Computes Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding outputEncoding
    (value D) := congrComputes (nativeComputes D) (native_exact D)
def machine : Machine := (computes D).machine
def time : Polynomial ℕ := (computes D).time
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial (computes D)
def storagePolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial D
theorem inFP : InFP Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding outputEncoding
    (value D) := (computes D).inFP
@[simp] theorem same_program : machine D=(sourcePrepare D).machine.compose
    ((save (s := s) (arity := arity)).machine.compose
      (finish (s := s) (arity := arity)).machine) := rfl
@[simp] theorem same_clock : time D=(nativeComputes D).time := rfl
@[simp] theorem same_lp_machine : uniformPoint.machine=RawSource.entryMachine := rfl
@[simp] theorem same_lp_clock : uniformPoint.time=RawSource.entryTime := rfl
@[simp] theorem point_same_program : (pointComputes D).machine=
    (MatrixCompiler.computes D).machine.compose RawSource.entryMachine := rfl
@[simp] theorem point_same_clock : (pointComputes D).time=
    (MatrixCompiler.computes D).time+2*((MatrixCompiler.computes D).outputBound.bound+1)+
      RawSource.entryTime.comp (MatrixCompiler.computes D).outputBound.bound := rfl
theorem original_matrix_word (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    Codec.inputEncoding.encode (MatrixCompiler.value D r)=Codec.encoding.encode (MatrixCompiler.raw D r) := rfl
theorem emitted_matrix_legal (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    Parsing.Source.parse (Codec.inputEncoding.encode (MatrixCompiler.value D r))=some (MatrixCompiler.value D r) :=
  (Parsing.Source.parse_some_iff _ _).mpr rfl
theorem matrix_query_width (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    (Codec.inputEncoding.encode (MatrixCompiler.value D r)).length≤
      (MatrixCompiler.computes D).outputBound.bound.eval
        (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r).length :=
  MatrixCompiler.output_bits D r
theorem average_return_width
    (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    (Codec.outputEncoding.encode (CommonSupportPoint.value (MatrixCompiler.value D r))).length≤
      (CommonSupportProgram.Source.computes.outputBound.bound.comp
        (MatrixCompiler.computes D).outputBound.bound).eval
          (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r).length := by
  apply (CommonSupportProgram.Source.output_bound (MatrixCompiler.value D r)).trans
  rw [Polynomial.eval_comp]
  exact natPolynomial_eval_mono CommonSupportProgram.Source.computes.outputBound.bound
    (matrix_query_width D r)
theorem execution (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer (outputEncoding.encode (value D r))) ((computes D).outputs r).steps :=
  ((computes D).outputs r).evals_in_steps
theorem steps_bound (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    ((computes D).outputs r).steps≤(time D).eval
      (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r).length :=
  ((computes D).outputs r).steps_le_m
theorem primitive_bound (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    primitiveCost (machine D) ((computes D).outputs r).steps
      (some (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r)))≤
      (primitivePolynomial D).eval (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r).length :=
  computes_primitive_cost (computes D) r
theorem output_bound (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    (outputEncoding.encode (value D r)).length≤(computes D).outputBound.bound.eval
      (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r).length :=
  (computes D).outputBound.length_le r
theorem prefix_storage (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity))
    (t : ℕ) (ht : t≤((computes D).outputs r).steps) (c : (machine D).Config)
    (hc : (fun p => p.bind (machine D).computer.step)^[t]
      (some (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r)))=some c) :
    stackSize c.stk≤(storagePolynomial D).eval
      (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r).length := by
  have hs := (machine D).run_size_le _ c t hc
  rw [Machine.size_init] at hs
  have hb := Nat.mul_le_mul_right (machine D).primitiveBudget (ht.trans ((computes D).outputs r).steps_le_m)
  apply hs.trans
  simpa only [storagePolynomial,primitivePolynomial,FixedFieldMachines.primitivePolynomial,machine,time,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.add_le_add_left hb (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r).length

theorem result_run_iff (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity))
    (out : Result) :
    (∃ steps, RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer (outputEncoding.encode out)) steps) ↔ value D r=out := by
  constructor
  · rintro ⟨steps,hrun⟩
    apply outputEncoding.encode_injective
    exact Optimization.Infrastructure.OutputUniqueness.machine_output_unique (machine D) _ _ _
      ((computes D).outputs r).steps steps (execution D r) hrun
  · intro he
    exact ⟨((computes D).outputs r).steps,by simpa only [he] using execution D r⟩
theorem negative_run_iff (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    (∃ steps, RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer [true,false]) steps) ↔
        ¬∃ w, Relaxation.Feasible (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) w :=
  (result_run_iff D r (some none)).trans (infeasible_original_iff D r)
theorem no_malformed_run (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    ¬∃ steps, RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer [false]) steps := by
  intro hrun
  exact not_malformed D r ((result_run_iff D r none).mp hrun)
theorem point_run_sound (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity))
    (y : Payload) (steps : ℕ) (hrun : RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer (true::true::payloadEncoding.encode y)) steps) :
    Codec.Solution (MatrixCompiler.raw D r) y.1 ∧
      Relaxation.Feasible (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) (weights D r y.1) ∧
      (∀ c : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Coordinate r,
        0<weights D r y.1 c.1 c.2 ↔ Relaxation.Candidate
          (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) c.1 c.2) ∧
      (∀ c : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Coordinate r,
        weights D r y.1 c.1 c.2=0 ↔ ¬Relaxation.Candidate
          (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) c.1 c.2) :=
  common_sound D r y ((result_run_iff D r (some (some y))).mp ⟨steps,hrun⟩)
theorem point_run_mask (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity))
    (y : Payload) (steps : ℕ) (hrun : RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer (true::true::payloadEncoding.encode y)) steps) :
    y.2.2=CandidateExecution.Responses.truth D r :=
  mask_original D r y ((result_run_iff D r (some (some y))).mp ⟨steps,hrun⟩)
theorem point_run_addresses (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity))
    (y : Payload) (steps : ℕ) (hrun : RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer (true::true::payloadEncoding.encode y)) steps) :
    y=payload r y.1 ∧
      y.2.1.length=(MatrixCompiler.raw D r).dimension ∧
      (∀ j : Fin (MatrixCompiler.raw D r).dimension,
        y.2.1.getD j.val (defaultColumn,0)=
          (ColumnOrder.encode r (ColumnOrder.order r j),
            weights D r y.1 (ColumnOrder.order r j).1 (ColumnOrder.order r j).2)) :=
  addressed_output D r y ((result_run_iff D r (some (some y))).mp ⟨steps,hrun⟩)
theorem feasible_run_iff (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    (∃ y steps, RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (Holant.LocalDrafts.Tractability.EOEvaluation.Source.inputEncoding.encode r))
      (haltList (machine D).computer (true::true::payloadEncoding.encode y)) steps) ↔
        ∃ w, Relaxation.Feasible (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) w := by
  constructor
  · rintro ⟨y,steps,hrun⟩
    exact ⟨weights D r y.1,(point_run_sound D r y steps hrun).2.1⟩
  · intro hf
    obtain ⟨y,hy⟩ := complete D r hf
    have ho : outputEncoding.encode (some (some y)) = true :: true :: payloadEncoding.encode y := rfl
    exact ⟨y,((computes D).outputs r).steps,by simpa only [hy, ho] using execution D r⟩

/-- Sole source theorem: every response concerns this internally emitted
matrix and this original graph. No answer branch is supplied by the caller. -/
theorem top (r : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Input (s := s) (arity := arity)) :
    (value D r≠none) ∧
    (value D r=some none ↔ ¬∃ w, Relaxation.Feasible
      (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) w) ∧
    (∀ y, value D r=some (some y) →
      Codec.Solution (MatrixCompiler.raw D r) y.1 ∧
      Relaxation.Feasible (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) (weights D r y.1) ∧
      (∀ c : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Coordinate r,
        0<weights D r y.1 c.1 c.2 ↔ Relaxation.Candidate
          (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) c.1 c.2) ∧
      (∀ c : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Coordinate r,
        weights D r y.1 c.1 c.2=0 ↔ ¬Relaxation.Candidate
          (Holant.LocalDrafts.Tractability.EOEvaluation.Source.network D r) c.1 c.2)) ∧
    (∀ y, value D r=some (some y) → y.2.2=CandidateExecution.Responses.truth D r) ∧
    (∀ y, value D r=some (some y) → y=payload r y.1 ∧
      y.2.1.length=(MatrixCompiler.raw D r).dimension ∧
      ∀ j : Fin (MatrixCompiler.raw D r).dimension,
        y.2.1.getD j.val (defaultColumn,0)=
          (ColumnOrder.encode r (ColumnOrder.order r j),
            weights D r y.1 (ColumnOrder.order r j).1 (ColumnOrder.order r j).2)) :=
  ⟨not_malformed D r,infeasible_original_iff D r,common_sound D r,mask_original D r,addressed_output D r⟩

end Source
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOCommonPointSource
