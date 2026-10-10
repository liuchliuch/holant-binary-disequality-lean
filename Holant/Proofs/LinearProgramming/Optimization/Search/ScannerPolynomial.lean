import Holant.Proofs.LinearProgramming.Optimization.Search.Scanner
import Holant.Proofs.LinearProgramming.Support.SumProgram

/-!
Polynomial retiming of the SAME Scanner.computes.
The independent Support.SumProgram supplies the actual suffix-denominator
bound. Outer states keep the original query and at most one of
the generated tags, so their encoded size is derived, never caller supplied.
This proves a separator subprogram, not a full LP polynomial-time solver.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.ScannerPolynomial
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
open Codec CutProgram Scanner
open Holant.LocalDrafts.RemoteWork.RationalLP.Support
noncomputable section

def dotTiming : Timing Scanner.dotComputes :=
  (Timing.ofPoly Scanner.termsComputes).andThen SumProgram.timing

def violatesTiming : Timing Scanner.violatesComputes := by
  let offset := (pairComputes (Scanner.cutQuery.andThen CutProgram.baseComputes)
    (Scanner.source.andThen PrecisionProgram.epsilonComputes)).andThen RationalArithmetic.additionComputes
  exact ((Timing.ofPoly offset).pair dotTiming).andThen (Timing.ofPoly Comparison.rationalLess)

def stepTiming : Timing Scanner.stepComputes := by
  let chosen := fixedListComputes Scanner.cellEncoding tagEncoding (fun p (_ : Unit) => p.1)
    (fun _ => Scanner.tag) [()]
  let old := (Wiring.secondComputes tagEncoding Scanner.accEncoding).andThen
    (Wiring.secondComputes Scanner.encoding Scanner.answerEncoding)
  let prepare := violatesTiming.pair (Timing.ofPoly (identityComputes Scanner.cellEncoding))
  let flag := Wiring.firstComputes encodingBoolBool Scanner.cellEncoding
  let ctx := Wiring.secondComputes encodingBoolBool Scanner.cellEncoding
  let result := ifComputes flag (ctx.andThen chosen) (ctx.andThen old)
  exact (prepare.andThen (Timing.ofPoly (pairComputes (ctx.andThen Scanner.query) result))).congr
    (fun p => rfl)

theorem fold_answer_shape (q : Scanner.Query) (ts : List Tag) :
    (ts.foldr Scanner.step (q,[])).2=[] ∨
      ∃ t∈ts, (ts.foldr Scanner.step (q,[])).2=[t] := by
  induction ts with
  | nil => exact Or.inl rfl
  | cons t ts ih =>
    simp only [List.foldr_cons,Scanner.step,Scanner.step_context]
    cases h : Scanner.violates q t with
    | false =>
      simp only [h,Bool.false_eq_true,↓reduceIte]
      rcases ih with he | ⟨u,hu,he⟩
      · exact Or.inl he
      · exact Or.inr ⟨u,by simp [hu],he⟩
    | true => exact Or.inr ⟨t,by simp,by simp only [h,↓reduceIte]⟩

private theorem member_bytes {A : Type} (e : Encoding A Bool) (xs : List A)
    (a : A) (ha : a∈xs) : (e.encode a).length≤((framedListEncoding e).encode xs).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ht
    · simp only [framedListEncoding,framedListEncode,List.length_cons,
        List.length_append,frame_length]
      omega
    · have h := ih ht
      simp only [framedListEncoding,framedListEncode,List.length_cons,List.length_append,frame_length] at h ⊢
      omega

theorem answer_bytes (q : Scanner.Query) (ts : List Tag) (k : ℕ) :
    (Scanner.answerEncoding.encode ((ts.drop k).foldr Scanner.step (q,[])).2).length≤
      2*(Scanner.answerEncoding.encode ts).length+3 := by
  rcases fold_answer_shape q (ts.drop k) with he | ⟨t,ht,he⟩
  · rw [he]
    simp [Scanner.answerEncoding,framedListEncoding,framedListEncode]
  · have hm := member_bytes tagEncoding ts t (List.mem_of_mem_drop ht)
    change (tagEncoding.encode t).length≤(framedListEncode tagEncoding ts).length at hm
    rw [he]
    simp only [Scanner.answerEncoding,framedListEncoding,framedListEncode,List.length_cons,
      List.length_append,List.length_nil,frame_length]
    omega

def foldEncoding := ReverseFold.encoding tagEncoding Scanner.accEncoding
def inputEncoding := ReverseFold.inputEncoding tagEncoding Scanner.accEncoding
def initial (q : Scanner.Query) (ts : List Tag) :
    ReverseFold.State (A := Tag) (B := Scanner.Acc) :=
  ReverseFold.start (ts,(q,([] : List Tag)))
def next := ReverseFold.step (false,0,false) Scanner.step

theorem actual_state_bytes (q : Scanner.Query) (ts : List Tag) (k : ℕ) :
    (foldEncoding.encode ((next^[k]) (initial q ts))).length≤
      3*(inputEncoding.encode (ts,(q,[]))).length+6 := by
  rw [initial,next,ReverseFold.iterate_start]
  have ha := answer_bytes q ts (ts.length-k)
  have hn : ts.length≤(Scanner.answerEncoding.encode ts).length := by
    have hlist := framedListEncoding_length_lower tagEncoding ts
    change 2*ts.length+1≤(Scanner.answerEncoding.encode ts).length at hlist
    omega
  have hctx := Scanner.step_context (ts.drop (ts.length-k)) (q,[])
  simp only [foldEncoding,inputEncoding,ReverseFold.encoding,ReverseFold.inputEncoding,
    ReverseFold.tailEncoding,Scanner.accEncoding,pairEncoding_length,
    UnaryBinary.unaryEncoding,List.length_replicate,hctx]
  change 2*(Scanner.answerEncoding.encode ts).length+1+
    (2*(ts.length-k)+1+(2*(Scanner.encoding.encode q).length+1+
      (Scanner.answerEncoding.encode ((ts.drop (ts.length-k)).foldr Scanner.step (q,[])).2).length))≤_
  have hnil : (Scanner.answerEncoding.encode ([] : List Tag)).length=1 := rfl
  rw [hnil]
  simp only [Scanner.answerEncoding,framedListEncoding] at ha hn ⊢
  omega

def timing : Timing Scanner.computes := by
  let initial := pairComputes (identityComputes Scanner.encoding)
    (constantComputes Scanner.encoding Scanner.answerEncoding [])
  let prepare := pairComputes
    ((Wiring.firstComputes Codec.inputEncoding pointEncoding).andThen Scanner.tagsComputes) initial
  let p := Timing.ofPoly prepare
  let W := 3*p.width+6
  let fold := Fold.after tagEncoding Scanner.accEncoding (false,0,false) Scanner.step
    p stepTiming W (fun q k => by
      have h := actual_state_bytes q (Scanner.tags q.1) k
      have hp := p.output_length q
      change (foldEncoding.encode ((next^[k]) (ScannerPolynomial.initial q (Scanner.tags q.1)))).length≤
        W.eval (Scanner.encoding.encode q).length
      change (inputEncoding.encode (Scanner.tags q.1,(q,[]))).length≤
        p.width.eval (Scanner.encoding.encode q).length at hp
      simp only [W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      exact h.trans (by omega))
  exact fold.andThen (Timing.ofPoly (Wiring.secondComputes Scanner.encoding Scanner.answerEncoding))

def computes : Computes Scanner.encoding Scanner.answerEncoding Scanner.value := timing.computes

theorem same_machine : computes.machine=Scanner.computes.machine := rfl
theorem same_steps (q : Scanner.Query) : (computes.outputs q).steps=(Scanner.computes.outputs q).steps := rfl

theorem physical_cost (q : Scanner.Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (Turing.initList computes.machine.computer (Scanner.encoding.encode q)))≤
      (primitivePolynomial computes).eval (Scanner.encoding.encode q).length := computes_primitive_cost computes q

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.ScannerPolynomial
