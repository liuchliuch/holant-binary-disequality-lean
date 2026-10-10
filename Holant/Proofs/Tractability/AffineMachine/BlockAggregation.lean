import Holant.Proofs.Tractability.AffineMachine.TabulatePhase


namespace Holant.LocalDrafts.Tractability.AffineMachine.BlockAggregation

open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open ProductMachine
noncomputable section

def row (n : ℕ) (r : RawBlocks.Row) : EncodedTable.Row :=
  (r.1, (List.range n).map (fun j => SamplePrograms.parity (SamplePrograms.single j) r.2))

def rowInputEncoding := pairEncoding UnaryBinary.unaryEncoding RawBlocks.rowEncoding

noncomputable def rowComputes : Computes rowInputEncoding EncodedTable.rowEncoding (fun x => row x.1 x.2) := by
  let n := Wiring.firstComputes UnaryBinary.unaryEncoding RawBlocks.rowEncoding
  let r := Wiring.secondComputes UnaryBinary.unaryEncoding RawBlocks.rowEncoding
  let rhs := r.andThen (Wiring.firstComputes encodingBoolBool (framedListEncoding encodingNatBool))
  let ports := r.andThen (Wiring.secondComputes encodingBoolBool (framedListEncoding encodingNatBool))
  let context := Wiring.firstComputes rowInputEncoding UnaryBinary.unaryEncoding
  let index := Wiring.secondComputes rowInputEncoding UnaryBinary.unaryEncoding
  let cell := (pairComputes (index.andThen SamplePrograms.singleComputes)
    (context.andThen ports)).andThen SamplePrograms.parityComputes
  let matrix := WireLists.tabulate rowInputEncoding encodingBoolBool Prod.fst n
    (fun x j => SamplePrograms.parity (SamplePrograms.single j) x.2.2) cell
  exact pairComputes rhs matrix

variable {s b : ℕ} {arity : ℕ → ℕ}
abbrev Block := RawBlocks.Block (s := s) (b := b)
abbrev Label := RawCode.Label (s := s) (b := b)
abbrev Input := ℕ × List (Block (s := s) (b := b))
def inputEncoding := pairEncoding UnaryBinary.unaryEncoding
  (framedListEncoding (RawBlocks.blockEncoding (s := s) (b := b)))
abbrev Output := EncodedTable.Data × Expr (Label (s := s) (b := b))
def outputEncoding := pairEncoding EncodedTable.encoding
  (Expr.encoding (FamilyField.labelEncoding (s := s) (b := b)))

def supportRows (bs : List (Block (s := s) (b := b))) := bs.flatMap (fun b => b.2.1)
def phaseTerms (bs : List (Block (s := s) (b := b))) := bs.flatMap (fun b => b.2.2)
def scaleCode (bs : List (Block (s := s) (b := b))) := Expr.product (bs.map (fun b => Expr.literal b.1))
def sample (x : Input (s := s) (b := b)) (mask : SamplePrograms.Mask) := SamplePrograms.phase mask (phaseTerms x.2)

def value (x : Input (s := s) (b := b)) : Output (s := s) (b := b) :=
  ((x.1, (supportRows x.2).map (row x.1), TabulatePhase.value Prod.fst sample x), scaleCode x.2)

noncomputable def blockTail := Wiring.secondComputes (FamilyField.labelEncoding (s := s) (b := b))
  (pairEncoding RawBlocks.rowsEncoding RawBlocks.phaseEncoding)
noncomputable def rowsComputes : Computes (framedListEncoding (RawBlocks.blockEncoding (s := s) (b := b)))
    RawBlocks.rowsEncoding supportRows :=
  AccessPrograms.flatMap RawBlocks.blockEncoding RawBlocks.rowEncoding (fun b => b.2.1)
    (blockTail.andThen (Wiring.firstComputes RawBlocks.rowsEncoding RawBlocks.phaseEncoding))
noncomputable def termsComputes : Computes (framedListEncoding (RawBlocks.blockEncoding (s := s) (b := b)))
    RawBlocks.phaseEncoding phaseTerms :=
  AccessPrograms.flatMap RawBlocks.blockEncoding Templates.recordEncoding (fun b => b.2.2)
    (blockTail.andThen (Wiring.secondComputes RawBlocks.rowsEncoding RawBlocks.phaseEncoding))

noncomputable def scaleComputes : Computes (framedListEncoding (RawBlocks.blockEncoding (s := s) (b := b)))
    (Expr.encoding FamilyField.labelEncoding) scaleCode :=
  Bytecode.finish (Bytecode.product RawBlocks.blockEncoding FamilyField.labelEncoding
    (fun b => Expr.literal b.1)
    ((Wiring.firstComputes FamilyField.labelEncoding (pairEncoding RawBlocks.rowsEncoding RawBlocks.phaseEncoding)).andThen
      (Bytecode.literal FamilyField.labelEncoding)))

noncomputable def sampleComputes : Computes (pairEncoding (inputEncoding (s := s) (b := b)) SamplePrograms.maskEncoding)
    ResidueCells.encoding4 (fun x => sample x.1 x.2) := by
  let context := Wiring.firstComputes (inputEncoding (s:=s) (b:=b)) SamplePrograms.maskEncoding
  let blocks := context.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding (framedListEncoding (RawBlocks.blockEncoding (s:=s) (b:=b))))
  exact (pairComputes (Wiring.secondComputes (inputEncoding (s:=s) (b:=b)) SamplePrograms.maskEncoding)
    (blocks.andThen termsComputes)).andThen SamplePrograms.phaseComputes

noncomputable def computes : Computes (inputEncoding (s := s) (b := b)) outputEncoding value := by
  let count := Wiring.firstComputes UnaryBinary.unaryEncoding (framedListEncoding (RawBlocks.blockEncoding (s:=s) (b:=b)))
  let blocks := Wiring.secondComputes UnaryBinary.unaryEncoding (framedListEncoding (RawBlocks.blockEncoding (s:=s) (b:=b)))
  let rows := (pairComputes count (blocks.andThen rowsComputes)).andThen
    (mapListComputes UnaryBinary.unaryEncoding RawBlocks.rowEncoding EncodedTable.rowEncoding row rowComputes)
  let phase := TabulatePhase.computes inputEncoding Prod.fst count sample sampleComputes
  exact pairComputes (pairComputes count (pairComputes rows phase)) (blocks.andThen scaleComputes)

noncomputable def fromRaw (D : Assembly.Family s b arity) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) outputEncoding
      (fun r => value (2 * r.val.edges.length, RawBlocks.blocks D r)) := by
  let edgeCount := edgeCountComputes s b arity
  let dim : Computes (RawClosedNetwork.validatedEncoding s b arity) UnaryBinary.unaryEncoding
      (fun r => 2*r.val.edges.length) := congrComputes ((pairComputes edgeCount edgeCount).andThen AccessPrograms.unaryAdd)
    (fun r => by simp [two_mul])
  exact (pairComputes dim (RawBlocks.computes D)).andThen computes

theorem primitive_bound (D : Assembly.Family s b arity)
    (r : FixedGadgetSubstitution.Compiler.Input s b arity) :
    let w := fromRaw D
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (fromRaw D) r

end
end Holant.LocalDrafts.Tractability.AffineMachine.BlockAggregation
