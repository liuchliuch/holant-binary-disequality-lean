import Holant.Proofs.Tractability.AffineMachine.ConstraintRewrite


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.FreeRewrite

open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open EncodedTable

def headLinear (d : Data) := linear d 0
def neighbors (d : Data) : List Bool :=
  (List.range (d.1 - 1)).map (fun j => decide (mixed d 0 (j + 1) ≠ 0))
def supportRows (d : Data) : List Row :=
  if headLinear d = 0 then [(false, neighbors d)] else
    if headLinear d = 2 then [(true, neighbors d)] else []

noncomputable def headComputes : Computes encoding ResidueCells.encoding4 headLinear :=
  ((phaseData.andThen phaseLinear).andThen (getDComputes ResidueCells.encoding4 0 0))

noncomputable def smaller : Computes encoding UnaryBinary.unaryEncoding (fun d => d.1 - 1) :=
  count.andThen Endpoints.unaryPredecessorComputes

noncomputable def neighborsComputes : Computes encoding bitsEncoding neighbors := by
  let firstRow := ((phaseData.andThen phaseMixed).andThen (getDComputes vectorEncoding 0 []))
  let old := Wiring.firstComputes encoding UnaryBinary.unaryEncoding
  let j := (Wiring.secondComputes encoding UnaryBinary.unaryEncoding).andThen WireLists.succComputes
  let coeff := AccessPrograms.get ResidueCells.encoding4 0 (old.andThen firstRow) j
  let bit := coeff.andThen (ResidueCells.test4 (fun q => decide (q ≠ 0)))
  exact WireLists.tabulate encoding encodingBoolBool (fun d => d.1 - 1) smaller _ bit

noncomputable def supportComputes : Computes encoding rowsEncoding supportRows := by
  let singleton (b : Bool) := fixedListComputes encoding rowEncoding (fun d (_ : Unit) => (b, neighbors d))
    (fun _ => pairComputes (constantComputes encoding encodingBoolBool b) neighborsComputes) [()]
  exact congrComputes (ifComputes (headComputes.andThen (ResidueCells.test4 (fun q => decide (q = 0))))
    (singleton false) (ifComputes (headComputes.andThen (ResidueCells.test4 (fun q => decide (q = 2))))
      (singleton true) (constantComputes encoding rowsEncoding []))) (fun d => by simp [supportRows])

abbrev Query := Data × SamplePrograms.Mask
def queryEncoding := pairEncoding encoding SamplePrograms.maskEncoding
def tailWord (x : Query) := (List.range x.1.1).map
  (fun k => if k = 0 then false else SamplePrograms.at x.2 (k - 1))
def parity (x : Query) := DensePrograms.dot (neighbors x.1) (DensePrograms.word (x.1.1 - 1) x.2)
def sample (d : Data) (m : SamplePrograms.Mask) : ZMod 4 :=
  let q := DensePrograms.phaseValue (d, tailWord (d, m))
  if headLinear d = 1 then q - FiniteCore.bit4 (parity (d, m)) else
    if headLinear d = 3 then q + FiniteCore.bit4 (parity (d, m)) else q

noncomputable def source : Computes queryEncoding encoding Prod.fst := Wiring.firstComputes _ _
noncomputable def mask : Computes queryEncoding SamplePrograms.maskEncoding Prod.snd := Wiring.secondComputes _ _

noncomputable def tailWordComputes : Computes queryEncoding bitsEncoding tailWord := by
  let old := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let zero := (pairComputes k (constantComputes _ UnaryBinary.unaryEncoding 0)).andThen (equalComputes UnaryBinary.unaryEncoding)
  let prev := (k.andThen Endpoints.unaryPredecessorComputes).andThen UnaryBinary.computes
  let bit := ifComputes zero (constantComputes _ encodingBoolBool false)
    ((pairComputes (old.andThen mask) prev).andThen SamplePrograms.atComputes)
  exact WireLists.tabulate queryEncoding encodingBoolBool (fun x => x.1.1) (source.andThen count) _ (congrComputes bit (fun x => by simp))

noncomputable def parityComputes : Computes queryEncoding encodingBoolBool parity :=
  (pairComputes (source.andThen neighborsComputes)
    ((pairComputes (source.andThen smaller) mask).andThen DensePrograms.wordComputes)).andThen DensePrograms.dotComputes

noncomputable def sampleComputes : Computes queryEncoding ResidueCells.encoding4 (fun x => sample x.1 x.2) := by
  let phase := (pairComputes source tailWordComputes).andThen DensePrograms.phaseComputes
  let bit := parityComputes.andThen ResidueCells.bool4
  let head := source.andThen headComputes
  exact congrComputes (ifComputes (head.andThen (ResidueCells.test4 (fun q => decide (q = 1))))
    (AccessPrograms.residue (· - ·) phase bit)
    (ifComputes (head.andThen (ResidueCells.test4 (fun q => decide (q = 3))))
      (AccessPrograms.residue (· + ·) phase bit) phase)) (fun x => by simp [sample])

def value (d : Data) : Data :=
  (d.1 - 1, supportRows d, TabulatePhase.value (fun d : Data => d.1 - 1) sample d)

noncomputable def computes : Computes encoding encoding value :=
  pairComputes smaller (pairComputes supportComputes
    (TabulatePhase.computes encoding (fun d => d.1 - 1) smaller sample sampleComputes))

theorem dimension_value (d : Data) : (value d).1 = d.1 - 1 := rfl
theorem rows_value (d : Data) : (value d).2.1.length ≤ 1 := by
  unfold value supportRows
  split_ifs <;> simp
theorem row_width (d : Data) (r : Row) (hr : r ∈ (value d).2.1) : r.2.length = d.1 - 1 := by
  simp only [value, supportRows] at hr
  split_ifs at hr <;> simp_all [neighbors]

end Holant.LocalDrafts.Tractability.AffineMachine.FreeRewrite
