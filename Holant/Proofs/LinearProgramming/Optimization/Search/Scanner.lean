import Holant.Proofs.LinearProgramming.Complexity.ListLemmas
import Holant.Proofs.LinearProgramming.Optimization.CutProgram
import Holant.Proofs.LinearProgramming.Support.SumProgram
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
Actual variable dot-product and first-violated-constraint Boolean-stack scan.
The query retains the original Codec.Input together with rational coordinates;
no compiled constraint table or correct separator is supplied by the caller.
The reverse physical fold replaces its answer at EVERY violated earlier row,
so it returns the first violation in box/equation, negative/positive order.
FiniteComputes is intentional: a uniform polynomial bound for all rational
partial sums and scanner configurations is not claimed by this file.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Scanner
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler

open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
open Codec CutProgram
open scoped BigOperators

abbrev Query := Codec.Input × List ℚ
abbrev Acc := Query × List Tag
def encoding := pairEncoding Codec.inputEncoding pointEncoding
def answerEncoding := framedListEncoding tagEncoding
def accEncoding := pairEncoding encoding answerEncoding
def cellEncoding := pairEncoding tagEncoding accEncoding
def faces (equation : Bool) (n : ℕ) : List Tag :=
  (List.range n).flatMap (fun j => [(equation,j,false),(equation,j,true)])
def tags (d : Codec.Input) : List Tag := faces false d.val.dimension++faces true d.val.rowCount
def terms (q : Query) (t : Tag) : List ℚ :=
  (List.range q.1.val.dimension).map (fun j => coefficient (q.1,t) j*q.2.getD j 0)
def violates (q : Query) (t : Tag) : Bool :=
  decide (base (q.1,t)+Thickening.epsilon q.1.val < (terms q t).sum)
def step (t : Tag) (s : Acc) : Acc :=
  (s.1,if violates s.1 t then [t] else s.2)
def value (q : Query) : List Tag := ((tags q.1).foldr step (q,[])).2

theorem step_context (ts : List Tag) (s : Acc) : (ts.foldr step s).1=s.1 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa only [List.foldr_cons,step] using ih

theorem fold_find (q : Query) (ts : List Tag) :
    (ts.foldr step (q,[])).2=(ts.find? (violates q)).toList := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldr_cons,step,step_context]
    cases h : violates q t <;> simp [h,List.find?_cons,ih]

theorem tags_exact (d : Codec.Input) :
    tags d=(Separation.constraints d.val).map (constraintTag d.val) := by
  have hr (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  simp only [tags,faces,Separation.constraints,List.map_append,List.map_flatMap]
  congr 1 <;> rw [← hr, List.flatMap_map] <;> rfl

theorem dot_exact (d : Codec.Input) (xs : List ℚ) (c : Separation.Constraint d.val) :
    (terms (d,xs) (constraintTag d.val c)).sum=
      Separation.lhs d.val c (fun j => xs.getD j.val 0) := by
  rw [terms,DensePrograms.range_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  rw [coefficient_correct]

theorem violates_exact (d : Codec.Input) (xs : List ℚ) (c : Separation.Constraint d.val) :
    violates (d,xs) (constraintTag d.val c)=
      decide (Separation.offset d.val c<Separation.lhs d.val c (fun j => xs.getD j.val 0)) := by
  have he := congrArg Prod.snd (CutProgram.correct d c)
  change base (d,constraintTag d.val c)+Thickening.epsilon d.val=Separation.offset d.val c at he
  simp only [violates,dot_exact,he]

theorem value_exact (d : Codec.Input) (xs : List ℚ) :
    value (d,xs)=((Separation.separate d.val (fun j => xs.getD j.val 0)).toList).map
      (constraintTag d.val) := by
  rw [value,fold_find,tags_exact]
  unfold Separation.separate
  rw [List.find?_map]
  simp only [Function.comp_def,violates_exact]
  cases Separation.constraints d.val |>.find? (fun c =>
    decide (Separation.offset d.val c < Separation.lhs d.val c (fun j => xs.getD j.val 0))) <;> rfl

theorem empty_iff (d : Codec.Input) (xs : List ℚ) :
    value (d,xs)=[] ↔ Thickening.At d.val (Thickening.epsilon d.val) (fun j => xs.getD j.val 0) := by
  rw [value_exact,← Separation.none_iff]
  cases Separation.separate d.val (fun j => xs.getD j.val 0) <;> simp

theorem success_original (d : Codec.Input) (xs : List ℚ) (h : value (d,xs)=[]) :
    ∃ x, Feasible d.val x :=
  (Thickening.nonempty_iff d.val).mp ⟨_,(empty_iff d xs).mp h⟩

theorem zero_reject (d : Codec.Input) (xs : List ℚ) (c : Separation.Constraint d.val)
    (hc : Separation.separate d.val (fun j => xs.getD j.val 0)=some c)
    (hz : Separation.normal d.val c=0) : ¬∃ x, Feasible d.val x :=
  Separation.zero_cut_reject d.val _ c hc hz

noncomputable section
def query : Computes cellEncoding encoding (fun p : Tag × Acc => p.2.1) :=
  (Wiring.secondComputes tagEncoding accEncoding).andThen (Wiring.firstComputes _ _)
def tag : Computes cellEncoding tagEncoding (fun p : Tag × Acc => p.1) := Wiring.firstComputes _ _
def source : Computes cellEncoding Codec.inputEncoding (fun p : Tag × Acc => p.2.1.1) :=
  query.andThen (Wiring.firstComputes _ _)
def point : Computes cellEncoding pointEncoding (fun p : Tag × Acc => p.2.1.2) :=
  query.andThen (Wiring.secondComputes _ _)
def cutQuery : Computes cellEncoding queryEncoding (fun p : Tag × Acc => (p.2.1.1,p.1)) :=
  pairComputes source tag

def termComputes : Computes (pairEncoding cellEncoding UnaryBinary.unaryEncoding) rationalEncoding
    (fun p => coefficient (p.1.2.1.1,p.1.1) p.2*p.1.2.1.2.getD p.2 0) := by
  let ctx := Wiring.firstComputes cellEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes cellEncoding UnaryBinary.unaryEncoding
  let a := (pairComputes (ctx.andThen cutQuery) j).andThen cellComputes
  let x := AccessPrograms.get rationalEncoding 0 (ctx.andThen point) j
  exact (pairComputes a x).andThen RationalArithmetic.multiplicationComputes

def termsComputes : Computes cellEncoding pointEncoding (fun p : Tag × Acc => terms p.2.1 p.1) := by
  let raw : Computes cellEncoding Codec.encoding (fun p : Tag × Acc => p.2.1.1.val) :=
    recode source id (fun _ => rfl) (fun _ => rfl)
  exact WireLists.tabulate cellEncoding rationalEncoding (fun p => p.2.1.1.val.dimension)
    (raw.andThen Parsing.dimension) _ termComputes

/-- Reuse only the already physical rational-sum helper; no EO backsolver is
copied or changed. Its finite time bound is not relabelled polynomial. -/
def dotComputes : FiniteComputes cellEncoding rationalEncoding
    (fun p : Tag × Acc => (terms p.2.1 p.1).sum) :=
  (FiniteComputes.ofPoly termsComputes).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram.sumComputes

def violatesComputes : FiniteComputes cellEncoding encodingBoolBool
    (fun p : Tag × Acc => violates p.2.1 p.1) := by
  let offset := (pairComputes (cutQuery.andThen baseComputes)
    (source.andThen PrecisionProgram.epsilonComputes)).andThen RationalArithmetic.additionComputes
  exact ((FiniteComputes.ofPoly offset).pair dotComputes).andThen
    (FiniteComputes.ofPoly Comparison.rationalLess)

def stepComputes : FiniteComputes cellEncoding accEncoding (fun p : Tag × Acc => step p.1 p.2) := by
  let chosen := fixedListComputes cellEncoding tagEncoding (fun p (_ : Unit) => p.1)
    (fun _ => tag) [()]
  let old := (Wiring.secondComputes tagEncoding accEncoding).andThen
    (Wiring.secondComputes encoding answerEncoding)
  let prepare := violatesComputes.pair (FiniteComputes.ofPoly (identityComputes cellEncoding))
  let flag := Wiring.firstComputes encodingBoolBool cellEncoding
  let ctx := Wiring.secondComputes encodingBoolBool cellEncoding
  let result := ifComputes flag (ctx.andThen chosen) (ctx.andThen old)
  exact (prepare.andThen (FiniteComputes.ofPoly
    (pairComputes (ctx.andThen query) result))).congr (fun p => rfl)

def facesComputes (eqn : Bool) : Computes UnaryBinary.unaryEncoding answerEncoding (faces eqn) := by
  let pairSigns := fixedListComputes UnaryBinary.unaryEncoding tagEncoding
    (fun j sign => (eqn,j,sign))
    (fun sign => pairComputes (constantComputes _ encodingBoolBool eqn)
      (pairComputes (identityComputes UnaryBinary.unaryEncoding)
        (constantComputes _ encodingBoolBool sign))) [false,true]
  exact (UnaryRange.computes).andThen
    (AccessPrograms.flatMap UnaryBinary.unaryEncoding tagEncoding _ pairSigns)

def tagsComputes : Computes Codec.inputEncoding answerEncoding tags := by
  let raw : Computes Codec.inputEncoding Codec.encoding (fun d : Codec.Input => d.val) :=
    recode (identityComputes Codec.inputEncoding) id (fun _ => rfl) (fun _ => rfl)
  let n := raw.andThen Parsing.dimension
  let m := (raw.andThen Parsing.rows).andThen (WireLists.lengthComputes rowEncoding)
  refine congrComputes ((pairComputes (n.andThen (facesComputes false)) (m.andThen (facesComputes true))).andThen
    (WireLists.append tagEncoding)) ?_
  intro d
  change faces false d.val.dimension ++ faces true d.val.rows.length = tags d
  rw [d.property.1]
  rfl

def computes : FiniteComputes encoding answerEncoding value := by
  let initial := pairComputes (identityComputes encoding)
    (constantComputes encoding answerEncoding [])
  let prepare := pairComputes ((Wiring.firstComputes Codec.inputEncoding pointEncoding).andThen tagsComputes) initial
  let loop := ReverseFold.computes
    tagEncoding accEncoding (false,0,false) step stepComputes
  exact ((FiniteComputes.ofPoly prepare).andThen loop).andThen
    (FiniteComputes.ofPoly (Wiring.secondComputes encoding answerEncoding))

theorem physical_cost (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (Turing.initList computes.machine.computer (encoding.encode q)))≤
      computes.time (encoding.encode q).length*computes.machine.primitiveBudget :=
  computes.primitive_bound q
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Scanner
