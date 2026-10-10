import Holant.Proofs.LinearProgramming.Support.CommonSupportPoint
import Holant.Proofs.LinearProgramming.Support.SumProgram
import Holant.Proofs.LinearProgramming.Support.OptionalValue
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionMapInterface
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionAny
import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.RationalInverse
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.PivotProgram

/-!
Concrete common-support machine on the unchanged original input bytes.
All n coordinate queries, fallback copies, n+1 point rows, rational sums,
normalization, division and framing are physically composed. The eager
infeasible branch is charged by the same composed Computes witness.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.CommonSupportProgram
open Codec Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines StackProtocol GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local irreducible] AllDimensionExactPoint.Source.computes

private theorem range_map {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

private theorem getD_ofFn {A : Type} {n : ℕ} (f : Fin n → A) (i : Fin n) (d : A) :
    (List.ofFn f).getD i.val d = f i := by simp [List.getD_eq_getElem]

private abbrev Context := Codec.Input × Option (List ℚ)
private def contextEncoding := pairEncoding Codec.inputEncoding Codec.outputEncoding
private def contextValue (d : Codec.Input) : Context := (d,AllDimensionExactPoint.Source.top d)
private def prepare : Computes Codec.inputEncoding contextEncoding contextValue :=
  pairComputes (identityComputes Codec.inputEncoding) AllDimensionExactPoint.Source.computes
private def original : Computes contextEncoding Codec.inputEncoding (fun c : Context => c.1) :=
  Wiring.firstComputes _ _
private def base : Computes contextEncoding Codec.outputEncoding (fun c : Context => c.2) :=
  Wiring.secondComputes _ _
private def rawOriginal : Computes contextEncoding Codec.encoding (fun c : Context => c.1.val) :=
  recode original id (fun _ => rfl) (fun _ => rfl)
private def dimension : Computes contextEncoding UnaryBinary.unaryEncoding
    (fun c : Context => c.1.val.dimension) := rawOriginal.andThen Parsing.dimension

private def normalize (n : ℕ) (xs : List ℚ) : List ℚ :=
  (List.range n).map (fun j => xs.getD j 0)
private def normalizedEncoding := pairEncoding UnaryBinary.unaryEncoding Codec.pointEncoding
private def normalizeComputes : Computes normalizedEncoding Codec.pointEncoding
    (fun x : ℕ × List ℚ => normalize x.1 x.2) := by
  let n := Wiring.firstComputes UnaryBinary.unaryEncoding Codec.pointEncoding
  let rows := Wiring.secondComputes UnaryBinary.unaryEncoding Codec.pointEncoding
  let ctx := Wiring.firstComputes normalizedEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes normalizedEncoding UnaryBinary.unaryEncoding
  exact WireLists.tabulate normalizedEncoding rationalEncoding Prod.fst n
    (fun x j => x.2.getD j 0) (AccessPrograms.get rationalEncoding 0 (ctx.andThen rows) j)

private def normalizedBase (c : Context) : List ℚ := normalize c.1.val.dimension (c.2.getD [])
private def normalizedBaseComputes : Computes contextEncoding Codec.pointEncoding normalizedBase :=
  (pairComputes dimension (base.andThen (Holant.LocalDrafts.RemoteWork.RationalLP.Support.OptionalValue.getDComputes
    Codec.pointEncoding []))).andThen normalizeComputes

/-- The cell accepts every natural cursor; well-formedness follows from the
original typed d, even outside the range. Only j<n is actually tabulated. -/
private def thresholdNat (d : Codec.Input) (j : ℕ) : Codec.Input :=
  ⟨ThresholdProgram.rawValue (d.val,j,InputBounds.denominator d.val),
    ThresholdProgram.wellFormed d j (InputBounds.denominator d.val)⟩
private def cellEncoding := pairEncoding contextEncoding UnaryBinary.unaryEncoding
private def thresholdComputes : Computes cellEncoding Codec.inputEncoding
    (fun q : Context × ℕ => thresholdNat q.1.1 q.2) := by
  let ctx := Wiring.firstComputes contextEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes contextEncoding UnaryBinary.unaryEncoding
  let src := ctx.andThen rawOriginal
  let den := src.andThen ExactSolve.DenominatorProgram.computes
  let ready : Computes cellEncoding ThresholdProgram.queryEncoding
      (fun q : Context × ℕ => (q.1.1.val,q.2,InputBounds.denominator q.1.1.val)) :=
    pairComputes src (pairComputes j den)
  exact recode (ready.andThen ThresholdProgram.computes) id (fun _ => rfl) (fun _ => rfl)

private def columnValue (q : Context × ℕ) : Option (List ℚ) :=
  AllDimensionExactPoint.Source.top (thresholdNat q.1.1 q.2)
private def columnComputes : Computes cellEncoding Codec.outputEncoding columnValue :=
  thresholdComputes.andThen AllDimensionExactPoint.Source.computes
private def returnedEncoding := pairEncoding cellEncoding Codec.outputEncoding
private def returnedComputes : Computes cellEncoding returnedEncoding
    (fun q : Context × ℕ => (q,columnValue q)) :=
  pairComputes (identityComputes cellEncoding) columnComputes

private def selectedList (q : (Context × ℕ) × Option (List ℚ)) : List ℚ :=
  q.2.getD (q.1.1.2.getD [])
private def selectedListComputes : Computes returnedEncoding Codec.pointEncoding selectedList := by
  let old := Wiring.firstComputes cellEncoding Codec.outputEncoding
  let ctx := old.andThen (Wiring.firstComputes contextEncoding UnaryBinary.unaryEncoding)
  let ans := Wiring.secondComputes cellEncoding Codec.outputEncoding
  exact (pairComputes ans (ctx.andThen base)).andThen
    (Holant.LocalDrafts.RemoteWork.RationalLP.Support.OptionalValue.chooseComputes Codec.pointEncoding [])
private def projectedComputes : Computes returnedEncoding Codec.pointEncoding
    (fun q : (Context × ℕ) × Option (List ℚ) => normalize q.1.1.1.val.dimension (selectedList q)) := by
  let old := Wiring.firstComputes cellEncoding Codec.outputEncoding
  let ctx := old.andThen (Wiring.firstComputes contextEncoding UnaryBinary.unaryEncoding)
  exact (pairComputes (ctx.andThen dimension) selectedListComputes).andThen normalizeComputes
private def cellValue (c : Context) (j : ℕ) : List ℚ :=
  normalize c.1.val.dimension ((columnValue (c,j)).getD (c.2.getD []))
private def cellComputes : Computes cellEncoding Codec.pointEncoding
    (fun q : Context × ℕ => cellValue q.1 q.2) := returnedComputes.andThen projectedComputes

private def tableEncoding := framedListEncoding Codec.pointEncoding
private def family (c : Context) : List (List ℚ) :=
  (List.range c.1.val.dimension).map (cellValue c) ++ [normalizedBase c]
private def familyComputes : Computes contextEncoding tableEncoding family := by
  let columns := WireLists.tabulate contextEncoding Codec.pointEncoding
    (fun c : Context => c.1.val.dimension) dimension cellValue cellComputes
  let last := fixedListComputes contextEncoding Codec.pointEncoding
    (fun c (_ : Unit) => normalizedBase c) (fun _ => normalizedBaseComputes) [()]
  exact (pairComputes columns last).andThen (WireLists.append Codec.pointEncoding)
private def savedEncoding := pairEncoding contextEncoding tableEncoding
private def save : Computes contextEncoding savedEncoding (fun c : Context => (c,family c)) :=
  pairComputes (identityComputes contextEncoding) familyComputes
private def savedContext : Computes savedEncoding contextEncoding (fun q : Context × List (List ℚ) => q.1) :=
  Wiring.firstComputes _ _
private def savedTable : Computes savedEncoding tableEncoding (fun q : Context × List (List ℚ) => q.2) :=
  Wiring.secondComputes _ _
private def savedDimension := savedContext.andThen dimension

private def termsEncoding := pairEncoding savedEncoding UnaryBinary.unaryEncoding
private def terms (q : (Context × List (List ℚ)) × ℕ) : List ℚ :=
  q.1.2.map (fun row => row.getD q.2 0)
private def termsComputes : Computes termsEncoding Codec.pointEncoding terms := by
  let src := Wiring.firstComputes savedEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes savedEncoding UnaryBinary.unaryEncoding
  let ctx := Wiring.firstComputes termsEncoding Codec.pointEncoding
  let row := Wiring.secondComputes termsEncoding Codec.pointEncoding
  exact AccessPrograms.map Codec.pointEncoding rationalEncoding (src.andThen savedTable)
    (fun q row => row.getD q.2 0) (AccessPrograms.get rationalEncoding 0 row (ctx.andThen j))

/-- This is the SAME old reverse-fold sum machine, with its existing proof
of actual suffix/register widths. It is not an unproved finite-to-poly lift. -/
private def sumComputes : Computes Codec.pointEncoding rationalEncoding List.sum :=
  Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram.computes
private def scaleComputes : Computes savedEncoding rationalEncoding
    (fun q : Context × List (List ℚ) => 1/(q.1.1.val.dimension+1 : ℕ)) := by
  let m := savedDimension.andThen WireLists.succComputes
  let integer := ((m.andThen UnaryBinary.computes).andThen RationalArithmetic.natCastComputes)
  exact congrComputes ((integer.andThen ExactSolve.PivotProgram.integerCast).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.RationalInverse.inverseComputes) (fun _ => by simp only [Function.comp_apply, id_eq, Nat.succ_eq_add_one, Int.cast_natCast, one_div])

private def coordinate (q : Context × List (List ℚ)) (j : ℕ) : ℚ :=
  (terms (q,j)).sum/(q.1.1.val.dimension+1 : ℕ)
private def coordinateComputes : Computes termsEncoding rationalEncoding
    (fun q : (Context × List (List ℚ)) × ℕ => coordinate q.1 q.2) := by
  let ctx := Wiring.firstComputes savedEncoding UnaryBinary.unaryEncoding
  exact congrComputes ((pairComputes (termsComputes.andThen sumComputes)
    (ctx.andThen scaleComputes)).andThen RationalArithmetic.multiplicationComputes)
      (fun q => by simp only [Function.comp_apply, coordinate, one_div, div_eq_mul_inv, one_mul])
private def averaged (q : Context × List (List ℚ)) : List ℚ :=
  (List.range q.1.1.val.dimension).map (coordinate q)
private def averagedComputes : Computes savedEncoding Codec.pointEncoding averaged :=
  WireLists.tabulate savedEncoding rationalEncoding (fun q : Context × List (List ℚ) => q.1.1.val.dimension)
    savedDimension coordinate coordinateComputes

private def presence (e : Encoding (List ℚ) Bool) :
    Computes (optionEncoding e) encodingBoolBool Option.isSome :=
  congrComputes ((OptionMap.computes (constantComputes e encodingBoolBool true)).andThen OptionAny.computes)
    (fun q => by cases q <;> rfl)
private def someComputes : Computes Codec.pointEncoding Codec.outputEncoding
    (fun xs => some xs) :=
  recode (joinComputes (constantComputes Codec.pointEncoding Frame.wordEncoding [true])
    (encodeComputes Codec.pointEncoding)) id (fun _ => rfl) (fun _ => rfl)
private def finishValue (q : Context × List (List ℚ)) : Option (List ℚ) :=
  if q.1.2.isSome then some (averaged q) else none
private def finish : Computes savedEncoding Codec.outputEncoding finishValue :=
  ifComputes ((savedContext.andThen base).andThen (presence Codec.pointEncoding))
    (averagedComputes.andThen someComputes) (constantComputes savedEncoding Codec.outputEncoding none)
private def nativeValue (d : Codec.Input) : Option (List ℚ) :=
  finishValue (contextValue d,family (contextValue d))
private def nativeComputes : Computes Codec.inputEncoding Codec.outputEncoding nativeValue :=
  prepare.andThen (save.andThen finish)

private theorem threshold_fin (d : Codec.Input) (j : Fin d.val.dimension) :
    thresholdNat d j.val=CommonSupportPoint.columnInput d j := rfl
private theorem cell_exact (d : Codec.Input) (base : List ℚ) (j : Fin d.val.dimension) :
    cellValue (d,some base) j.val=List.ofFn (CommonSupportPoint.selected d base j.castSucc) := by
  change normalize d.val.dimension ((CommonSupportPoint.columnOutput d j).getD base) = _
  cases he : CommonSupportPoint.columnOutput d j with
  | none =>
    simp only [Option.getD_none, normalize, range_map, CommonSupportPoint.selected,
      Fin.lastCases_castSucc, he]
    rfl
  | some xs =>
    simp only [Option.getD_some, normalize, range_map, CommonSupportPoint.selected,
      Fin.lastCases_castSucc, he]
    rfl

private theorem family_exact (d : Codec.Input) (base : List ℚ) :
    family (d,some base)=List.ofFn (fun i => List.ofFn (CommonSupportPoint.selected d base i)) := by
  rw [family,range_map]
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append]
  congr 1
  · congr 1
    funext j
    exact cell_exact d base j
  · simp only [CommonSupportPoint.selected,Fin.lastCases_last,normalizedBase,
      Option.getD_some,normalize,range_map]
    rfl

private theorem averaged_exact (d : Codec.Input) (base : List ℚ) :
    averaged ((d,some base),family (d,some base))=CommonSupportPoint.averageList d base := by
  rw [averaged,range_map]
  congr 1
  funext j
  have ht : (terms (((d,some base),family (d,some base)),j.val)).sum=
      ∑ i, CommonSupportPoint.selected d base i j := by
    simp only [terms,family_exact,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
      getD_ofFn]
  simp only [coordinate,ht,CommonSupportPoint.averageList,CommonSupportPoint.average]

private theorem native_exact (d : Codec.Input) : nativeValue d=CommonSupportPoint.value d := by
  cases hb : AllDimensionExactPoint.Source.top d with
  | none => simp only [nativeValue,contextValue,hb,finishValue,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
      CommonSupportPoint.value,Option.map_none]
  | some base =>
    simp only [nativeValue,contextValue,hb,finishValue,Option.isSome_some,↓reduceIte,
      CommonSupportPoint.value,Option.map_some,averaged_exact]

private theorem family_length (c : Context) : (family c).length=c.1.val.dimension+1 := by
  simp only [family,List.length_append,List.length_map,List.length_range,List.length_singleton]

namespace Source

/-- Sole typed original-system program; all point calls and averaging are
installed internally. No returned point or clock/capacity is an input. -/
def computes : Computes Codec.inputEncoding Codec.outputEncoding CommonSupportPoint.value :=
  congrComputes nativeComputes native_exact
def machine : Machine := computes.machine
def time : Polynomial ℕ := computes.time
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial computes
def storagePolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial

theorem inFP : InFP Codec.inputEncoding Codec.outputEncoding CommonSupportPoint.value := computes.inFP
@[simp] theorem same_program : machine=prepare.machine.compose (save.machine.compose finish.machine) := rfl
@[simp] theorem same_clock : time=nativeComputes.time := rfl
@[simp] theorem actual_sum_machine : sumComputes.machine=Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram.sumComputes.machine := SumProgram.same_machine
@[simp] theorem actual_sum_steps (xs : List ℚ) :
    (sumComputes.outputs xs).steps=(Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram.sumComputes.outputs xs).steps := SumProgram.same_steps xs
theorem collected_count (d : Codec.Input) :
    (family (contextValue d)).length=d.val.dimension+1 := family_length _
theorem original_column_input (d : Codec.Input) (j : Fin d.val.dimension) :
    thresholdNat d j.val=CommonSupportPoint.columnInput d j := threshold_fin d j
theorem execution (d : Codec.Input) : RunsExactly machine.computer.step
    (initList machine.computer (Codec.inputEncoding.encode d))
    (haltList machine.computer (Codec.outputEncoding.encode (CommonSupportPoint.value d)))
    (computes.outputs d).steps := (computes.outputs d).evals_in_steps
theorem time_bound (d : Codec.Input) : (computes.outputs d).steps≤time.eval (InputBounds.size d.val) :=
  (computes.outputs d).steps_le_m
theorem primitive_bound (d : Codec.Input) : primitiveCost machine (computes.outputs d).steps
    (some (initList machine.computer (Codec.inputEncoding.encode d)))≤
      primitivePolynomial.eval (InputBounds.size d.val) := computes_primitive_cost computes d
theorem output_bound (d : Codec.Input) :
    (Codec.outputEncoding.encode (CommonSupportPoint.value d)).length≤
      computes.outputBound.bound.eval (InputBounds.size d.val) := computes.outputBound.length_le d
theorem prefix_storage (d : Codec.Input) (t : ℕ) (ht : t≤(computes.outputs d).steps)
    (c : machine.Config) (hc : (fun p => p.bind machine.computer.step)^[t]
      (some (initList machine.computer (Codec.inputEncoding.encode d)))=some c) :
    stackSize c.stk≤storagePolynomial.eval (InputBounds.size d.val) := by
  have hs := machine.run_size_le _ c t hc
  rw [machine.size_init] at hs
  have hcost := Nat.mul_le_mul_right machine.primitiveBudget (ht.trans (computes.outputs d).steps_le_m)
  apply hs.trans
  simpa only [storagePolynomial,primitivePolynomial,FixedFieldMachines.primitivePolynomial,machine,time,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C,
    InputBounds.size, Codec.inputEncoding] using
      Nat.add_le_add_left hcost (Codec.inputEncoding.encode d).length

theorem response (d : Codec.Input) : Codec.Response d.val (CommonSupportPoint.value d) := by
  cases he : CommonSupportPoint.value d with
  | none => exact (CommonSupportPoint.none_iff d).mp he
  | some xs => exact (CommonSupportPoint.some_properties d xs he).1
theorem support (d : Codec.Input) (xs : List ℚ) (he : CommonSupportPoint.value d=some xs) :
    Codec.Solution d.val xs ∧
      (∀ j, 0<Codec.point d.val xs j ↔ Codec.Positive d.val j) ∧
      (∀ j, Codec.point d.val xs j=0 ↔ ¬Codec.Positive d.val j) :=
  CommonSupportPoint.some_properties d xs he


end Source
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.CommonSupportProgram
