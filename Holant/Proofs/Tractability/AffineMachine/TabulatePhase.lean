import Holant.Proofs.Tractability.AffineMachine.EncodedTable


namespace Holant.LocalDrafts.Tractability.AffineMachine.TabulatePhase

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler

variable {A : Type} (ea : Encoding A Bool) (size : A → ℕ)
  (count : Computes ea UnaryBinary.unaryEncoding size)
  (q : A → SamplePrograms.Mask → ZMod 4)
  (sample : Computes (pairEncoding ea SamplePrograms.maskEncoding) ResidueCells.encoding4 (fun x => q x.1 x.2))

def value (a : A) : EncodedTable.Phase :=
  (q a SamplePrograms.origin,
    (List.range (size a)).map (fun i => q a (SamplePrograms.single i) - q a SamplePrograms.origin),
    (List.range (size a)).map (fun i => (List.range (size a)).map (fun j =>
      q a (SamplePrograms.pair i j) - q a (SamplePrograms.single i) -
        q a (SamplePrograms.single j) + q a SamplePrograms.origin)))

noncomputable def zero : Computes ea ResidueCells.encoding4 (fun a => q a SamplePrograms.origin) :=
  (pairComputes (identityComputes ea) (constantComputes ea SamplePrograms.maskEncoding SamplePrograms.origin)).andThen sample

noncomputable def single : Computes (pairEncoding ea UnaryBinary.unaryEncoding) ResidueCells.encoding4
    (fun x => q x.1 (SamplePrograms.single x.2)) :=
  (pairComputes (Wiring.firstComputes ea UnaryBinary.unaryEncoding)
    ((Wiring.secondComputes ea UnaryBinary.unaryEncoding).andThen SamplePrograms.singleComputes)).andThen sample

noncomputable def linear : Computes (pairEncoding ea UnaryBinary.unaryEncoding) ResidueCells.encoding4
    (fun x => q x.1 (SamplePrograms.single x.2) - q x.1 SamplePrograms.origin) :=
  AccessPrograms.residue (· - ·) (single ea q sample)
    ((Wiring.firstComputes ea UnaryBinary.unaryEncoding).andThen (zero ea q sample))

noncomputable def mixed :
    Computes (pairEncoding (pairEncoding ea UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding)
      ResidueCells.encoding4 (fun x => q x.1.1 (SamplePrograms.pair x.1.2 x.2) -
        q x.1.1 (SamplePrograms.single x.1.2) - q x.1.1 (SamplePrograms.single x.2) + q x.1.1 SamplePrograms.origin) := by
  let first := Wiring.firstComputes (pairEncoding ea UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let context := first.andThen (Wiring.firstComputes ea UnaryBinary.unaryEncoding)
  let i := first.andThen (Wiring.secondComputes ea UnaryBinary.unaryEncoding)
  let j := Wiring.secondComputes (pairEncoding ea UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let pairSample := (pairComputes context ((pairComputes i j).andThen SamplePrograms.pairComputes)).andThen sample
  let qi := first.andThen (single ea q sample)
  let qj := (pairComputes context j).andThen (single ea q sample)
  exact AccessPrograms.residue (· + ·)
    (AccessPrograms.residue (· - ·) (AccessPrograms.residue (· - ·) pairSample qi) qj)
    (context.andThen (zero ea q sample))

noncomputable def computes : Computes ea EncodedTable.phaseEncoding (value size q) := by
  let lin := WireLists.tabulate ea ResidueCells.encoding4 size count
    (fun a i => q a (SamplePrograms.single i) - q a SamplePrograms.origin) (linear ea q sample)
  let row := WireLists.tabulate (pairEncoding ea UnaryBinary.unaryEncoding) ResidueCells.encoding4
    (fun x => size x.1) ((Wiring.firstComputes ea UnaryBinary.unaryEncoding).andThen count)
    (fun a j => q a.1 (SamplePrograms.pair a.2 j) - q a.1 (SamplePrograms.single a.2) -
      q a.1 (SamplePrograms.single j) + q a.1 SamplePrograms.origin) (mixed ea q sample)
  let mat := WireLists.tabulate ea EncodedTable.vectorEncoding size count
    (fun a i => (List.range (size a)).map (fun j => q a (SamplePrograms.pair i j) -
      q a (SamplePrograms.single i) - q a (SamplePrograms.single j) + q a SamplePrograms.origin)) row
  exact pairComputes (zero ea q sample) (pairComputes lin mat)

theorem primitive_bound (a : A) :
    let w := computes ea size count q sample
    primitiveCost w.machine (w.outputs a).steps
      (some (Turing.initList w.machine.computer (ea.encode a))) ≤
        (primitivePolynomial w).eval (ea.encode a).length :=
  computes_primitive_cost (computes ea size count q sample) a

end Holant.LocalDrafts.Tractability.AffineMachine.TabulatePhase
