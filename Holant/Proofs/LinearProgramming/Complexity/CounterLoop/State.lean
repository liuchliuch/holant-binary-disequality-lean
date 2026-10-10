import Holant.Proofs.LinearProgramming.Optimization.Search.StepProgram

/-! Rational LP physical resource implementation, adapted from the supplied reference.
Original-input initialization for the rounded LP countdown. The remaining
budget is stored in canonical BINARY, while the polynomial unary budget
producer is used once at initialization. Center and diagonal factor are
actually tabulated from the original dimension. No prepared search state,
feasible point, separator, or iteration certificate is an input.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators

open Codec
noncomputable section

abbrev State := ℕ × (Bool × StepProgram.Query)
def tailEncoding := pairEncoding encodingBoolBool StepProgram.encoding
def encoding := pairEncoding encodingNatBool tailEncoding
def bodyEncoding := pairEncoding encodingBoolBool encoding

def remaining (s : State) : ℕ := s.1
def answer (s : State) : Bool := s.2.1
def query (s : State) : StepProgram.Query := s.2.2
def stamp (r : ℕ) (b : Bool) (q : StepProgram.Query) : State := (r,b,q)

def counterComputes : Computes encoding encodingNatBool remaining := Wiring.firstComputes _ _
def tailComputes : Computes encoding tailEncoding Prod.snd := Wiring.secondComputes _ _
def answerComputes : Computes encoding encodingBoolBool answer :=
  tailComputes.andThen (Wiring.firstComputes encodingBoolBool StepProgram.encoding)
def queryComputes : Computes encoding StepProgram.encoding query :=
  tailComputes.andThen (Wiring.secondComputes encodingBoolBool StepProgram.encoding)

def radius (d : Input) : ℚ := 2*((d.val.dimension : ℚ)+1)
def initialCode (d : Input) : StorageProgram.Code :=
  (List.replicate d.val.dimension 0,
    (List.range d.val.dimension).map (fun i =>
      (List.range d.val.dimension).map (fun j => if i=j then radius d else 0)))
def initialQuery (d : Input) : StepProgram.Query := (d,initialCode d)
def initial (d : Input) : State := stamp (GridPrecision.iterations d.val) false (initialQuery d)

def radiusComputes : Computes inputEncoding rationalEncoding radius := by
  let n := (PrecisionProgram.dimensionComputes.andThen RationalArithmetic.natCastComputes).andThen
    PivotProgram.integerCast
  let plus := (pairComputes n (constantComputes inputEncoding rationalEncoding 1)).andThen
    RationalArithmetic.additionComputes
  exact (pairComputes (constantComputes inputEncoding rationalEncoding 2) plus).andThen
    RationalArithmetic.multiplicationComputes

def rowInputEncoding := pairEncoding inputEncoding UnaryBinary.unaryEncoding
def cellInputEncoding := pairEncoding rowInputEncoding UnaryBinary.unaryEncoding

def initialCell : Computes cellInputEncoding rationalEncoding
    (fun x : (Input × ℕ) × ℕ => if x.1.2=x.2 then radius x.1.1 else 0) := by
  let p := Wiring.firstComputes rowInputEncoding UnaryBinary.unaryEncoding
  let d := p.andThen (Wiring.firstComputes inputEncoding UnaryBinary.unaryEncoding)
  let i := p.andThen (Wiring.secondComputes inputEncoding UnaryBinary.unaryEncoding)
  let j := Wiring.secondComputes rowInputEncoding UnaryBinary.unaryEncoding
  let equal := (pairComputes i j).andThen Parsing.unaryEqual
  exact congrComputes (ifComputes equal (d.andThen radiusComputes)
    (constantComputes cellInputEncoding rationalEncoding 0)) (fun x => by simp)

def initialRow : Computes rowInputEncoding pointEncoding
    (fun x : Input × ℕ => (List.range x.1.val.dimension).map
      (fun j => if x.2=j then radius x.1 else 0)) :=
  WireLists.tabulate rowInputEncoding rationalEncoding (fun x => x.1.val.dimension)
    ((Wiring.firstComputes inputEncoding UnaryBinary.unaryEncoding).andThen BudgetProgram.dimension)
    (fun x j => if x.2=j then radius x.1 else 0) initialCell

def initialCodeComputes : Computes inputEncoding StorageProgram.encoding initialCode :=
  pairComputes (BudgetProgram.dimension.andThen (WireLists.replicate rationalEncoding 0))
    (WireLists.tabulate inputEncoding pointEncoding (fun d : Input => d.val.dimension)
      BudgetProgram.dimension (fun d i => (List.range d.val.dimension).map
        (fun j => if i=j then radius d else 0)) initialRow)

def initialQueryComputes : Computes inputEncoding StepProgram.encoding initialQuery :=
  pairComputes (identityComputes inputEncoding) initialCodeComputes

def budgetBinary : Computes inputEncoding encodingNatBool
    (fun d : Input => GridPrecision.iterations d.val) :=
  GridPrecision.countComputes.andThen UnaryBinary.computes

def prepare : Computes inputEncoding encoding initial :=
  pairComputes budgetBinary
    (pairComputes (constantComputes inputEncoding encodingBoolBool false) initialQueryComputes)

theorem initialCode_exact (d : Input) : initialCode d=StorageProgram.code (Containment.start d.val.dimension) := by
  unfold initialCode StorageProgram.code
  congr 1
  · change List.replicate d.val.dimension (0 : ℚ) = List.ofFn (fun _ : Fin d.val.dimension => (0 : ℚ))
    exact (List.ofFn_const _ _).symm
  · rw [DensePrograms.range_map]
    congr 1
    funext i
    rw [DensePrograms.range_map]
    congr 1
    funext j
    by_cases h : i=j
    · subst j
      simp [Containment.start,radius,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    · have hij : i.val≠j.val := fun hv => h (Fin.ext hv)
      simp [Containment.start,radius,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,h,hij]

def queryAt (d : Input) (k : ℕ) : StepProgram.Query :=
  (d,StorageProgram.code (RoundedTrajectory.run d.val k))

@[simp] theorem initialQuery_exact (d : Input) : initialQuery d=queryAt d 0 := by
  rw [initialQuery,initialCode_exact]
  rfl

theorem actual_round (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k<GridPrecision.iterations d.val) : StepProgram.value (queryAt d k)=queryAt d (k+1) :=
  StepProgram.actual_round d hn k hk

@[simp] theorem queryAt_source (d : Input) (k : ℕ) : (queryAt d k).1=d := rfl

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
