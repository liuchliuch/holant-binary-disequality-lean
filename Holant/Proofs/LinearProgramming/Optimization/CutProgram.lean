import Holant.Proofs.LinearProgramming.Optimization.PrecisionProgram
import Holant.Proofs.LinearProgramming.Optimization.Separation
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
Physical emission of every separation row from original input bytes. Dynamic
row/column lookup, signed unit rows, epsilon construction and framing are all
charged. This emits a selected constraint; Search.Scanner performs first-violated-row
selection with its physical variable-length dot-product scan.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.CutProgram
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
noncomputable section

/-- true selects an original equation row; false selects a box-coordinate row.
The final Bool selects the positive versus negative inequality. -/
abbrev Tag := Bool × (ℕ × Bool)
abbrev Query := Input × Tag
def tagEncoding := pairEncoding encodingBoolBool (pairEncoding UnaryBinary.unaryEncoding encodingBoolBool)
def queryEncoding := pairEncoding inputEncoding tagEncoding
def lineEncoding := pairEncoding pointEncoding rationalEncoding
def source : Computes queryEncoding inputEncoding Prod.fst := Wiring.firstComputes _ _
def tag := Wiring.secondComputes inputEncoding tagEncoding
def equation : Computes queryEncoding encodingBoolBool (fun q : Query => q.2.1) := tag.andThen (Wiring.firstComputes _ _)
def rest := tag.andThen (Wiring.secondComputes encodingBoolBool (pairEncoding UnaryBinary.unaryEncoding encodingBoolBool))
def index : Computes queryEncoding UnaryBinary.unaryEncoding (fun q : Query => q.2.2.1) := rest.andThen (Wiring.firstComputes _ _)
def positive : Computes queryEncoding encodingBoolBool (fun q : Query => q.2.2.2) := rest.andThen (Wiring.secondComputes _ _)
def raw : Computes queryEncoding encoding (fun q : Query => q.1.val) := recode source id (fun _ => rfl) (fun _ => rfl)

def coefficient (q : Query) (j : ℕ) : ℚ :=
  let a : ℚ := if q.2.1 then (((q.1.val.rows.getD q.2.2.1 []).getD j 0 : ℤ):ℚ)
    else if j=q.2.2.1 then 1 else 0
  if q.2.2.2 then a else -a
def base (q : Query) : ℚ :=
  if q.2.1 then if q.2.2.2 then (q.1.val.rhs.getD q.2.2.1 0:ℚ)
    else -(q.1.val.rhs.getD q.2.2.1 0:ℚ)
  else if q.2.2.2 then 1 else 0
def value (q : Query) : List ℚ × ℚ :=
  ((List.range q.1.val.dimension).map (coefficient q),base q+Thickening.epsilon q.1.val)

def cellComputes : Computes (pairEncoding queryEncoding UnaryBinary.unaryEncoding) rationalEncoding
    (fun q => coefficient q.1 q.2) := by
  let ctx := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let row := AccessPrograms.get rowEncoding [] ((ctx.andThen raw).andThen Parsing.rows) (ctx.andThen index)
  let entry := (AccessPrograms.get IntegerArithmetic.encoding 0 row j).andThen PivotProgram.integerCast
  let eq := (pairComputes j (ctx.andThen index)).andThen Parsing.unaryEqual
  let unit := ifComputes eq
    (constantComputes (pairEncoding queryEncoding UnaryBinary.unaryEncoding) rationalEncoding 1)
    (constantComputes (pairEncoding queryEncoding UnaryBinary.unaryEncoding) rationalEncoding 0)
  let a := ifComputes (ctx.andThen equation) entry unit
  exact congrComputes (ifComputes (ctx.andThen positive) a (a.andThen Comparison.rationalNegate))
    (fun q => by simp [coefficient,Function.comp_def])

def baseComputes : Computes queryEncoding rationalEncoding base := by
  let b := (AccessPrograms.get IntegerArithmetic.encoding 0 (raw.andThen Parsing.rhs) index).andThen PivotProgram.integerCast
  let signed := ifComputes positive b (b.andThen Comparison.rationalNegate)
  let unit := ifComputes positive (constantComputes queryEncoding rationalEncoding 1)
    (constantComputes queryEncoding rationalEncoding 0)
  exact ifComputes equation signed unit

def computes : Computes queryEncoding lineEncoding value := by
  let normal := WireLists.tabulate queryEncoding rationalEncoding (fun q => q.1.val.dimension)
    (raw.andThen Parsing.dimension) coefficient cellComputes
  let offset := (pairComputes baseComputes (source.andThen PrecisionProgram.epsilonComputes)).andThen
    RationalArithmetic.additionComputes
  exact pairComputes normal offset

def constraintTag (d : Raw) (c : Separation.Constraint d) : Tag :=
  match c.1 with
  | .inl j => (false,j.val,c.2)
  | .inr i => (true,i.val,c.2)

theorem coefficient_correct (d : Input) (c : Separation.Constraint d.val) (j : Fin d.val.dimension) :
    coefficient (d,constraintTag d.val c) j.val=Separation.normal d.val c j := by
  rcases c with ⟨c,b⟩
  cases c <;> cases b <;>
    simp [coefficient,constraintTag,Separation.normal,Raw.coefficient,Fin.ext_iff] <;> rfl

theorem correct (d : Input) (c : Separation.Constraint d.val) :
    value (d,constraintTag d.val c)=
      (List.ofFn (Separation.normal d.val c),Separation.offset d.val c) := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [value]
    · intro i hi hi'
      simpa [value] using coefficient_correct d c ⟨i,by simpa [value] using hi⟩
  · rcases c with ⟨c,b⟩
    cases c <;> cases b <;> simp [value,base,constraintTag,Separation.offset,Separation.base,Raw.constant]

theorem primitive_bound (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (initList computes.machine.computer (queryEncoding.encode q))) ≤
      (primitivePolynomial computes).eval (queryEncoding.encode q).length := computes_primitive_cost computes q

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.CutProgram
