import Holant.Proofs.Tractability.AffineMachine.BlockAggregation


namespace Holant.LocalDrafts.Tractability.AffineMachine.DensePrograms

set_option backward.isDefEq.respectTransparency false
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open EncodedTable

theorem range_map {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  rw [List.ofFn_eq_map, ← finRange_values, List.map_map]
  rfl

@[simp] theorem getD_ofFn {A : Type} {n : ℕ} (f : Fin n → A) (j : Fin n) (a : A) :
    (List.ofFn f).getD j.val a = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using j.isLt)]
  simp

def dot (row word : List Bool) : Bool := ResidueCells.parity
  ((List.range row.length).map (fun j => row.getD j false && word.getD j false))

noncomputable def dotComputes : Computes (pairEncoding bitsEncoding bitsEncoding) encodingBoolBool
    (fun x => dot x.1 x.2) := by
  let ea := pairEncoding bitsEncoding bitsEncoding
  let row := Wiring.firstComputes bitsEncoding bitsEncoding
  let word := Wiring.secondComputes bitsEncoding bitsEncoding
  let ctx := Wiring.firstComputes ea UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes ea UnaryBinary.unaryEncoding
  let bit := AccessPrograms.bool Bool.and
    (AccessPrograms.get encodingBoolBool false (ctx.andThen row) j)
    (AccessPrograms.get encodingBoolBool false (ctx.andThen word) j)
  exact (WireLists.tabulate ea encodingBoolBool (fun x => x.1.length)
    (row.andThen (WireLists.lengthComputes encodingBoolBool)) _ bit).andThen ResidueCells.parityComputes

def word (n : ℕ) (mask : SamplePrograms.Mask) : List Bool :=
  (List.range n).map (SamplePrograms.at mask)

noncomputable def wordComputes : Computes (pairEncoding UnaryBinary.unaryEncoding SamplePrograms.maskEncoding)
    bitsEncoding (fun x => word x.1 x.2) := by
  let ea := pairEncoding UnaryBinary.unaryEncoding SamplePrograms.maskEncoding
  let ctx := Wiring.firstComputes ea UnaryBinary.unaryEncoding
  let mask := ctx.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding SamplePrograms.maskEncoding)
  let j := (Wiring.secondComputes ea UnaryBinary.unaryEncoding).andThen UnaryBinary.computes
  exact WireLists.tabulate ea encodingBoolBool Prod.fst (Wiring.firstComputes _ _) _
    ((pairComputes mask j).andThen SamplePrograms.atComputes)

abbrev Query := Data × List Bool
def queryEncoding := pairEncoding encoding bitsEncoding

def linearValue (x : Query) (j : ℕ) : ZMod 4 :=
  linear x.1 j * FiniteCore.bit4 (x.2.getD j false)
def mixedValue (x : Query) (j k : ℕ) : ZMod 4 :=
  if j < k then mixed x.1 j k * FiniteCore.bit4 (x.2.getD j false) * FiniteCore.bit4 (x.2.getD k false) else 0
def phaseValue (x : Query) : ZMod 4 :=
  constant x.1 + ((List.range x.1.1).map (linearValue x)).sum +
    ((List.range x.1.1).map (fun j => ((List.range x.1.1).map (mixedValue x j)).sum)).sum

noncomputable def data : Computes queryEncoding encoding Prod.fst := Wiring.firstComputes _ _
noncomputable def assignment : Computes queryEncoding bitsEncoding Prod.snd := Wiring.secondComputes _ _
noncomputable def dimension := data.andThen count
noncomputable def lin := (data.andThen phaseData).andThen phaseLinear
noncomputable def mat := (data.andThen phaseData).andThen phaseMixed
noncomputable def base := (data.andThen phaseData).andThen phaseConstant

noncomputable def linearComputes : Computes (pairEncoding queryEncoding UnaryBinary.unaryEncoding)
    ResidueCells.encoding4 (fun x => linearValue x.1 x.2) := by
  let ctx := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  exact AccessPrograms.residue (· * ·)
    (AccessPrograms.get ResidueCells.encoding4 0 (ctx.andThen lin) j)
    ((AccessPrograms.get encodingBoolBool false (ctx.andThen assignment) j).andThen ResidueCells.bool4)

noncomputable def mixedComputes :
    Computes (pairEncoding (pairEncoding queryEncoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding)
      ResidueCells.encoding4 (fun x => mixedValue x.1.1 x.1.2 x.2) := by
  let first := Wiring.firstComputes (pairEncoding queryEncoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let ctx := first.andThen (Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding)
  let j := first.andThen (Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding)
  let k := Wiring.secondComputes (pairEncoding queryEncoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let less := (pairComputes (j.andThen UnaryBinary.computes) (k.andThen UnaryBinary.computes)).andThen Endpoints.lessComputes
  let row := AccessPrograms.get vectorEncoding [] (ctx.andThen mat) j
  let coeff := AccessPrograms.get ResidueCells.encoding4 0 row k
  let bitj := (AccessPrograms.get encodingBoolBool false (ctx.andThen assignment) j).andThen ResidueCells.bool4
  let bitk := (AccessPrograms.get encodingBoolBool false (ctx.andThen assignment) k).andThen ResidueCells.bool4
  exact congrComputes (ifComputes less
    (AccessPrograms.residue (· * ·) (AccessPrograms.residue (· * ·) coeff bitj) bitk)
    (constantComputes _ ResidueCells.encoding4 0))
    (fun x => by simp [mixedValue, Function.comp_def, EncodedTable.mixed])

noncomputable def phaseComputes : Computes queryEncoding ResidueCells.encoding4 phaseValue := by
  let linearSum := (WireLists.tabulate queryEncoding ResidueCells.encoding4 (fun x => x.1.1)
    dimension linearValue linearComputes).andThen ResidueCells.sum4
  let inner := (WireLists.tabulate (pairEncoding queryEncoding UnaryBinary.unaryEncoding) ResidueCells.encoding4
    (fun x => x.1.1.1) ((Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding).andThen dimension)
    (fun x k => mixedValue x.1 x.2 k) mixedComputes).andThen ResidueCells.sum4
  let mixedSum := (WireLists.tabulate queryEncoding ResidueCells.encoding4 (fun x => x.1.1)
    dimension (fun x j => ((List.range x.1.1).map (mixedValue x j)).sum) inner).andThen ResidueCells.sum4
  exact AccessPrograms.residue (· + ·) (AccessPrograms.residue (· + ·) base linearSum) mixedSum

theorem phaseValue_exact (d : Data) (h : Regular d) (w : List Bool) :
    phaseValue (d, w) = (EncodedTable.phase d h).eval (fun j => w.getD j.val false) := by
  simp [phaseValue, linearValue, mixedValue, EncodedTable.phase, QuadraticPhase.eval,
    FiniteCore.bit4, bitValue, range_map, List.sum_ofFn]

theorem dot_exact {n : ℕ} (a x : Fin n → Bool) :
    FiniteCore.bit2 (dot (List.ofFn a) (List.ofFn x)) =
      FiniteCore.dot (fun j => FiniteCore.bit2 (a j)) x := by
  rw [dot, ResidueCells.parity_value]
  have h (a b : Bool) : FiniteCore.bit2 (a && b) = FiniteCore.bit2 a * FiniteCore.bit2 b := by
    cases a <;> cases b <;> decide
  simp [FiniteCore.dot, h, range_map, getD_ofFn, Function.comp_def]

theorem primitive_bound (x : Query) :
    primitiveCost phaseComputes.machine (phaseComputes.outputs x).steps
      (some (Turing.initList phaseComputes.machine.computer (queryEncoding.encode x))) ≤
        (primitivePolynomial phaseComputes).eval (queryEncoding.encode x).length :=
  computes_primitive_cost phaseComputes x

end Holant.LocalDrafts.Tractability.AffineMachine.DensePrograms
