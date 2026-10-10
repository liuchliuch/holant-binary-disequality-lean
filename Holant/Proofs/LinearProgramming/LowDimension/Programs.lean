import Holant.Proofs.LinearProgramming.LowDimension.ZeroDim
import Holant.Proofs.LinearProgramming.LowDimension.OneDim
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.PivotProgram
import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.FirstTrue

/-! Physical low-dimensional point programs. All row scans, selection,
framing, arithmetic, and eager branches belong to fixed Boolean-stack machines. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.LowDimension.Programs
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP Foundation Support.MachineCombinators
open Foundation.Infrastructure
noncomputable section

def zeroChecks : Computes Codec.encoding (framedListEncoding encodingBoolBool) ZeroDim.checks := by
  let ctx := Wiring.firstComputes Codec.encoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes Codec.encoding UnaryBinary.unaryEncoding
  let rhs := AccessPrograms.get IntegerArithmetic.encoding 0 (ctx.andThen Foundation.Parsing.rhs) i
  let checked := (pairComputes rhs (constantComputes
    (pairEncoding Codec.encoding UnaryBinary.unaryEncoding) IntegerArithmetic.encoding 0)).andThen
    (equalComputes IntegerArithmetic.encoding)
  exact WireLists.tabulate Codec.encoding encodingBoolBool Codec.Raw.rowCount Foundation.Parsing.rowCount
    (fun d i => decide (d.rhs.getD i 0 = 0)) checked

def zeroAccepted : Computes Codec.encoding encodingBoolBool ZeroDim.accepted :=
  zeroChecks.andThen ResidueCells.all

def zero : Computes Codec.encoding Codec.outputEncoding ZeroDim.value :=
  ifComputes zeroAccepted
    (constantComputes Codec.encoding Codec.outputEncoding (some []))
    (constantComputes Codec.encoding Codec.outputEncoding none)

def pairEncodingZ := pairEncoding IntegerArithmetic.encoding IntegerArithmetic.encoding
def rowsEncoding := framedListEncoding pairEncodingZ

def rowsComputes : Computes Codec.encoding rowsEncoding OneDim.rows := by
  let ctx := Wiring.firstComputes Codec.encoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes Codec.encoding UnaryBinary.unaryEncoding
  let row := AccessPrograms.get Codec.rowEncoding [] (ctx.andThen Foundation.Parsing.rows) i
  let a := AccessPrograms.get IntegerArithmetic.encoding 0 row
    (constantComputes (pairEncoding Codec.encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding 0)
  let b := AccessPrograms.get IntegerArithmetic.encoding 0 (ctx.andThen Foundation.Parsing.rhs) i
  exact WireLists.tabulate Codec.encoding pairEncodingZ Codec.Raw.rowCount Foundation.Parsing.rowCount
    (fun d i => ((d.rows.getD i []).getD 0 0,d.rhs.getD i 0)) (pairComputes a b)

def nonzero (r : ℤ × ℤ) : Bool := decide (r.1 ≠ 0)
def index (rs : List (ℤ × ℤ)) : ℕ := rs.findIdx nonzero

theorem pick_index (rs : List (ℤ × ℤ)) :
    OneDim.pick rs = if index rs = rs.length then none else
      some (((rs.getD (index rs) (0,0)).2 : ℚ) / ((rs.getD (index rs) (0,0)).1 : ℚ)) := by
  induction rs with
  | nil => simp [OneDim.pick,index]
  | cons r rs ih =>
    rcases r with ⟨a,b⟩
    by_cases ha : a = 0
    · have hf : index ((a,b)::rs) = index rs + 1 := by
        simp [index,nonzero,ha,List.findIdx_cons]
      rw [hf]
      simpa only [OneDim.pick,ha,↓reduceIte,List.length_cons,
        Nat.add_right_cancel_iff,List.getD_cons_succ] using ih
    · simp [OneDim.pick,index,nonzero,ha,List.findIdx_cons]

def flags (rs : List (ℤ × ℤ)) : List Bool := rs.map nonzero

def nonzeroComputes : Computes pairEncodingZ encodingBoolBool nonzero := by
  let a := Wiring.firstComputes IntegerArithmetic.encoding IntegerArithmetic.encoding
  let eq := (pairComputes a (constantComputes pairEncodingZ IntegerArithmetic.encoding 0)).andThen
    (equalComputes IntegerArithmetic.encoding)
  exact congrComputes (AccessPrograms.bool (fun x _ => !x) eq
    (constantComputes pairEncodingZ encodingBoolBool false)) (fun r => by simp [nonzero])

def flagsComputes : Computes rowsEncoding (framedListEncoding encodingBoolBool) flags :=
  WireLists.mapComputes pairEncodingZ encodingBoolBool nonzero nonzeroComputes

def sentinel (rs : List (ℤ × ℤ)) : FirstTrue.Input := ⟨flags rs ++ [true],by simp⟩
def sentinelComputes : Computes rowsEncoding FirstTrue.inputEncoding sentinel := by
  let unframe := Bytecode.flatMap encodingBoolBool (fun b => [b]) (encodeComputes encodingBoolBool)
  let bits : Computes rowsEncoding Frame.wordEncoding flags :=
    congrComputes (flagsComputes.andThen unframe) (fun rs => by simp)
  exact recode (joinComputes bits (constantComputes rowsEncoding Frame.wordEncoding [true]))
    id (fun _ => rfl) (fun _ => rfl)

theorem sentinel_index (rs : List (ℤ × ℤ)) : FirstTrue.value (sentinel rs)=index rs := by
  change ((rs.map nonzero) ++ [true]).findIdx id = _
  induction rs with
  | nil => simp [index]
  | cons r rs ih =>
    by_cases h : r.1=0 <;> simp_all [index,nonzero,List.findIdx_cons]

def indexComputes : Computes rowsEncoding UnaryBinary.unaryEncoding index :=
  congrComputes (sentinelComputes.andThen FirstTrue.computes) sentinel_index

def ratioComputes : Computes pairEncodingZ rationalEncoding
    (fun r => (r.2 : ℚ)/(r.1 : ℚ)) := by
  let a := (Wiring.firstComputes IntegerArithmetic.encoding IntegerArithmetic.encoding).andThen
    Foundation.ExactSolve.PivotProgram.integerCast
  let b := (Wiring.secondComputes IntegerArithmetic.encoding IntegerArithmetic.encoding).andThen
    Foundation.ExactSolve.PivotProgram.integerCast
  exact congrComputes ((pairComputes b (a.andThen RationalInverse.inverseComputes)).andThen
    RationalArithmetic.multiplicationComputes) (fun _ => (div_eq_mul_inv _ _).symm)

def candidateRowsComputes : Computes rowsEncoding rationalEncoding
    (fun rs => (OneDim.pick rs).getD 1) := by
  let absent := (pairComputes indexComputes (WireLists.lengthComputes pairEncodingZ)).andThen
    Foundation.Parsing.unaryEqual
  let selected := AccessPrograms.get pairEncodingZ (0,0) (identityComputes rowsEncoding) indexComputes
  refine congrComputes (ifComputes absent (constantComputes rowsEncoding rationalEncoding 1)
    (selected.andThen ratioComputes)) ?_
  intro rs
  rw [pick_index]
  by_cases h : index rs=rs.length <;> simp [h]

def candidateComputes : Computes Codec.encoding rationalEncoding OneDim.candidate :=
  rowsComputes.andThen candidateRowsComputes

def boundedComputes : Computes Codec.encoding encodingBoolBool
    (fun d => decide (0 ≤ OneDim.candidate d ∧ OneDim.candidate d ≤ 1)) := by
  let zero := constantComputes Codec.encoding rationalEncoding 0
  let one := constantComputes Codec.encoding rationalEncoding 1
  let lower := (pairComputes zero candidateComputes).andThen Foundation.Comparison.rationalLe
  let upper := (pairComputes candidateComputes one).andThen Foundation.Comparison.rationalLe
  exact congrComputes (AccessPrograms.bool Bool.and lower upper) (fun d => by simp)

def rowChecks : Computes Codec.encoding (framedListEncoding encodingBoolBool)
    (fun d => (OneDim.rows d).map (fun r => decide ((r.1 : ℚ)*OneDim.candidate d=(r.2 : ℚ)))) := by
  let ctx := Wiring.firstComputes Codec.encoding pairEncodingZ
  let row := Wiring.secondComputes Codec.encoding pairEncodingZ
  let a := (row.andThen (Wiring.firstComputes IntegerArithmetic.encoding IntegerArithmetic.encoding)).andThen
    Foundation.ExactSolve.PivotProgram.integerCast
  let b := (row.andThen (Wiring.secondComputes IntegerArithmetic.encoding IntegerArithmetic.encoding)).andThen
    Foundation.ExactSolve.PivotProgram.integerCast
  let product := (pairComputes a (ctx.andThen candidateComputes)).andThen RationalArithmetic.multiplicationComputes
  let checked := (pairComputes product b).andThen (equalComputes rationalEncoding)
  exact AccessPrograms.map pairEncodingZ encodingBoolBool rowsComputes
    (fun d r => decide ((r.1 : ℚ)*OneDim.candidate d=(r.2 : ℚ))) checked

def oneAccepted : Computes Codec.encoding encodingBoolBool OneDim.accepted :=
  congrComputes (AccessPrograms.bool Bool.and boundedComputes (rowChecks.andThen ResidueCells.all))
    (fun d => by simp [OneDim.accepted,List.all_map,Function.comp_def])

def singletonComputes : Computes Codec.encoding Codec.pointEncoding
    (fun d => [OneDim.candidate d]) :=
  congrComputes (fixedListComputes Codec.encoding rationalEncoding
    (fun d (_ : Unit) => OneDim.candidate d) (fun _ => candidateComputes) [()]) (fun _ => by simp)

def someComputes : Computes Codec.encoding Codec.outputEncoding
    (fun d => some [OneDim.candidate d]) :=
  recode (joinComputes (constantComputes Codec.encoding Frame.wordEncoding [true])
    (singletonComputes.andThen (encodeComputes Codec.pointEncoding))) id (fun _ => rfl) (fun _ => rfl)

def one : Computes Codec.encoding Codec.outputEncoding OneDim.value :=
  ifComputes oneAccepted someComputes (constantComputes Codec.encoding Codec.outputEncoding none)

def zeroTyped : Computes Codec.inputEncoding Codec.outputEncoding (fun d => ZeroDim.value d.val) :=
  recode zero Subtype.val (fun _ => rfl) (fun _ => rfl)
def oneTyped : Computes Codec.inputEncoding Codec.outputEncoding (fun d => OneDim.value d.val) :=
  recode one Subtype.val (fun _ => rfl) (fun _ => rfl)
end
end Holant.LocalDrafts.RemoteWork.RationalLP.LowDimension.Programs
