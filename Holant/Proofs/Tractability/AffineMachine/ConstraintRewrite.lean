import Holant.Proofs.Tractability.AffineMachine.PivotPrograms


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.ConstraintRewrite

open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open EncodedTable

abbrev Context := Data × (ℕ × ℕ)
def contextEncoding := pairEncoding encoding (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
abbrev Query := Context × SamplePrograms.Mask
def queryEncoding := pairEncoding contextEncoding SamplePrograms.maskEncoding

def beforeBit (x : Query) (k : ℕ) : Bool :=
  if k = x.1.2.2 then false else SamplePrograms.at x.2 (if k = 0 then x.1.2.2 - 1 else k - 1)
def before (x : Query) := (List.range x.1.1.1).map (beforeBit x)
def pivotRow (c : Context) := c.1.2.1.getD c.2.1 (false, [])
def selectedBit (x : Query) := Bool.xor (pivotRow x.1).1 (DensePrograms.dot (pivotRow x.1).2 (before x))
def solve (x : Query) := (List.range x.1.1.1).map
  (fun k => if k = x.1.2.2 then selectedBit x else beforeBit x k)

noncomputable def source : Computes contextEncoding encoding Prod.fst := Wiring.firstComputes _ _
noncomputable def indices := Wiring.secondComputes encoding (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
noncomputable def rowIndex := indices.andThen (Wiring.firstComputes _ _)
noncomputable def columnIndex := indices.andThen (Wiring.secondComputes _ _)
noncomputable def pivotRowComputes : Computes contextEncoding rowEncoding pivotRow :=
  AccessPrograms.get rowEncoding (false, []) (source.andThen rows) rowIndex
noncomputable def context : Computes queryEncoding contextEncoding Prod.fst := Wiring.firstComputes _ _
noncomputable def mask : Computes queryEncoding SamplePrograms.maskEncoding Prod.snd := Wiring.secondComputes _ _
noncomputable def dimension := (context.andThen source).andThen count

noncomputable def beforeBitComputes : Computes (pairEncoding queryEncoding UnaryBinary.unaryEncoding)
    encodingBoolBool (fun x => beforeBit x.1 x.2) := by
  let old := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let j := (old.andThen context).andThen columnIndex
  let isPivot := (pairComputes k j).andThen (equalComputes UnaryBinary.unaryEncoding)
  let isZero := (pairComputes k (constantComputes _ UnaryBinary.unaryEncoding 0)).andThen
    (equalComputes UnaryBinary.unaryEncoding)
  let tailIndex := (ifComputes isZero j k).andThen Endpoints.unaryPredecessorComputes
  let bit := (pairComputes (old.andThen mask) (tailIndex.andThen UnaryBinary.computes)).andThen SamplePrograms.atComputes
  exact congrComputes (ifComputes isPivot (constantComputes _ encodingBoolBool false) bit)
    (fun x => by by_cases h : x.2 = 0 <;> simp [beforeBit, h])

noncomputable def beforeComputes : Computes queryEncoding bitsEncoding before :=
  WireLists.tabulate queryEncoding encodingBoolBool (fun x => x.1.1.1) dimension beforeBit beforeBitComputes

noncomputable def selectedComputes : Computes queryEncoding encodingBoolBool selectedBit := by
  let row := context.andThen pivotRowComputes
  let rhs := row.andThen (Wiring.firstComputes encodingBoolBool bitsEncoding)
  let coeffs := row.andThen (Wiring.secondComputes encodingBoolBool bitsEncoding)
  exact AccessPrograms.bool Bool.xor rhs ((pairComputes coeffs beforeComputes).andThen DensePrograms.dotComputes)

noncomputable def solveComputes : Computes queryEncoding bitsEncoding solve := by
  let old := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let j := (old.andThen context).andThen columnIndex
  let isPivot := (pairComputes k j).andThen (equalComputes UnaryBinary.unaryEncoding)
  let cell := ifComputes isPivot (old.andThen selectedComputes) beforeBitComputes
  exact WireLists.tabulate queryEncoding encodingBoolBool (fun x => x.1.1.1) dimension _
    (congrComputes cell (fun x => by simp))

def supportSample (x : Context × Row) (m : SamplePrograms.Mask) : Bool :=
  DensePrograms.dot x.2.2 (solve (x.1, m))
def supportRow (x : Context × Row) : Row :=
  (Bool.xor x.2.1 (supportSample x SamplePrograms.origin),
    (List.range (x.1.1.1 - 1)).map (fun j => Bool.xor (supportSample x (SamplePrograms.single j))
      (supportSample x SamplePrograms.origin)))
def rowContextEncoding := pairEncoding contextEncoding rowEncoding

noncomputable def supportSampleComputes : Computes (pairEncoding rowContextEncoding SamplePrograms.maskEncoding)
    encodingBoolBool (fun x => supportSample x.1 x.2) := by
  let old := Wiring.firstComputes rowContextEncoding SamplePrograms.maskEncoding
  let ctx := old.andThen (Wiring.firstComputes contextEncoding rowEncoding)
  let row := old.andThen (Wiring.secondComputes contextEncoding rowEncoding)
  let m := Wiring.secondComputes rowContextEncoding SamplePrograms.maskEncoding
  exact (pairComputes (row.andThen (Wiring.secondComputes encodingBoolBool bitsEncoding))
    ((pairComputes ctx m).andThen solveComputes)).andThen DensePrograms.dotComputes

noncomputable def supportRowComputes : Computes rowContextEncoding rowEncoding supportRow := by
  let ctx := Wiring.firstComputes contextEncoding rowEncoding
  let row := Wiring.secondComputes contextEncoding rowEncoding
  let rhs := row.andThen (Wiring.firstComputes encodingBoolBool bitsEncoding)
  let q0 := (pairComputes (identityComputes rowContextEncoding)
    (constantComputes rowContextEncoding SamplePrograms.maskEncoding SamplePrograms.origin)).andThen supportSampleComputes
  let old := Wiring.firstComputes rowContextEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes rowContextEncoding UnaryBinary.unaryEncoding
  let qj := (pairComputes old (j.andThen SamplePrograms.singleComputes)).andThen supportSampleComputes
  let cell := AccessPrograms.bool Bool.xor qj (old.andThen q0)
  let count := ((ctx.andThen source).andThen EncodedTable.count).andThen Endpoints.unaryPredecessorComputes
  exact pairComputes (AccessPrograms.bool Bool.xor rhs q0)
    (WireLists.tabulate rowContextEncoding encodingBoolBool (fun x => x.1.1.1 - 1) count _ cell)

def phaseSample (c : Context) (m : SamplePrograms.Mask) : ZMod 4 :=
  DensePrograms.phaseValue (c.1, solve (c, m))
noncomputable def phaseSampleComputes : Computes queryEncoding ResidueCells.encoding4 (fun x => phaseSample x.1 x.2) :=
  (pairComputes (context.andThen source) solveComputes).andThen DensePrograms.phaseComputes

def value (c : Context) : Data :=
  (c.1.1 - 1, c.1.2.1.map (fun r => supportRow (c, r)),
    TabulatePhase.value (fun c : Context => c.1.1 - 1) phaseSample c)

noncomputable def computes : Computes contextEncoding encoding value := by
  let count := (source.andThen EncodedTable.count).andThen Endpoints.unaryPredecessorComputes
  let rows := (pairComputes (identityComputes contextEncoding) (source.andThen EncodedTable.rows)).andThen
    (mapListComputes contextEncoding rowEncoding rowEncoding (fun c r => supportRow (c, r)) supportRowComputes)
  let phase := TabulatePhase.computes contextEncoding (fun c => c.1.1 - 1) count phaseSample phaseSampleComputes
  exact pairComputes count (pairComputes rows phase)

theorem dimension_value (c : Context) : (value c).1 = c.1.1 - 1 := rfl
theorem rows_value (c : Context) : (value c).2.1.length = c.1.2.1.length := by simp [value]
theorem row_width (c : Context) (r : Row) (hr : r ∈ (value c).2.1) : r.2.length = c.1.1 - 1 := by
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
  simp [supportRow]

end Holant.LocalDrafts.Tractability.AffineMachine.ConstraintRewrite
