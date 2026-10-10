import Holant.Proofs.Tractability.EOEvaluation.MatrixCells


namespace Holant.LocalDrafts.Tractability.EOEvaluation.MatrixCompiler
open Computability Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open AffineMachine RawColumns
namespace LP
abbrev Raw := TraversalCompletion.RationalLP.Codec.Raw
abbrev Input := TraversalCompletion.RationalLP.Codec.Input
abbrev rowEncoding := TraversalCompletion.RationalLP.Codec.rowEncoding
abbrev rowsEncoding := TraversalCompletion.RationalLP.Codec.rowsEncoding
abbrev encoding := TraversalCompletion.RationalLP.Codec.encoding
abbrev inputEncoding := TraversalCompletion.RationalLP.Codec.inputEncoding
end LP
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

def row (f : Column × ℕ → ℤ) (r : Source.Input (s := s) (arity := arity)) (i : ℕ) :=
  (columns r).map (fun c => f (c, i))
def vertexRows (r : Source.Input (s := s) (arity := arity)) :=
  (List.range r.val.vertices.length).map (row MatrixCells.normalization r)
def edgeRows (r : Source.Input (s := s) (arity := arity)) :=
  (List.range r.val.edges.length).map (row (MatrixCells.edge (s := s) (arity := arity)) r)
def zeroRows (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) :=
  (columns r).map (fun q => (columns r).map (fun c => MatrixCells.diagonal D (q, c)))

def raw (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) : LP.Raw where
  rowCount := r.val.vertices.length + r.val.edges.length + (columns r).length
  dimension := (columns r).length
  rows := vertexRows r ++ edgeRows r ++ zeroRows D r
  rhs := List.replicate r.val.vertices.length 1 ++ List.replicate (r.val.edges.length + (columns r).length) 0

theorem wellFormed (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) :
    (raw D r).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simp [raw, vertexRows, edgeRows, zeroRows, Nat.add_assoc]
  · simp [raw, Nat.add_assoc]
  · intro xs hx
    simp only [raw, List.mem_append, vertexRows, edgeRows, zeroRows, List.mem_map, or_assoc] at hx
    rcases hx with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ | ⟨q, _, rfl⟩ <;> simp [row, raw]

def value (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) : LP.Input :=
  ⟨raw D r, wellFormed D r⟩

def indexedEncoding := pairEncoding (Source.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding

private def rowComputes (f : Column × ℕ → ℤ)
    (cell : Computes MatrixCells.indexedEncoding IntegerArithmetic.encoding f) :
    Computes (indexedEncoding (s := s) (arity := arity)) LP.rowEncoding (fun x => row f x.1 x.2) := by
  let src := Wiring.firstComputes (Source.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  let idx := Wiring.secondComputes (Source.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  let ctx := Wiring.firstComputes (indexedEncoding (s := s) (arity := arity)) columnEncoding
  let col := Wiring.secondComputes (indexedEncoding (s := s) (arity := arity)) columnEncoding
  exact AccessPrograms.map columnEncoding IntegerArithmetic.encoding (src.andThen RawColumns.computes)
    (fun x c => f (c, x.2)) ((pairComputes col (ctx.andThen idx)).andThen cell)

def vertexRowsComputes : Computes (Source.inputEncoding (s := s) (arity := arity)) LP.rowsEncoding vertexRows :=
  WireLists.tabulate Source.inputEncoding LP.rowEncoding (fun r => r.val.vertices.length)
    (vertexCountComputes s 1 arity) _ (rowComputes MatrixCells.normalization MatrixCells.normalizationComputes)

def edgeRowsComputes : Computes (Source.inputEncoding (s := s) (arity := arity)) LP.rowsEncoding edgeRows :=
  WireLists.tabulate Source.inputEncoding LP.rowEncoding (fun r => r.val.edges.length)
    (edgeCountComputes s 1 arity) _ (rowComputes (MatrixCells.edge (s := s) (arity := arity)) MatrixCells.edgeComputes)

def zeroRowsComputes (D : Source.Family s arity) :
    Computes (Source.inputEncoding (s := s) (arity := arity)) LP.rowsEncoding (zeroRows D) := by
  let ea := pairEncoding (Source.inputEncoding (s := s) (arity := arity)) columnEncoding
  let src := Wiring.firstComputes (Source.inputEncoding (s := s) (arity := arity)) columnEncoding
  let q := Wiring.secondComputes (Source.inputEncoding (s := s) (arity := arity)) columnEncoding
  let ctx := Wiring.firstComputes ea columnEncoding
  let col := Wiring.secondComputes ea columnEncoding
  let inner := AccessPrograms.map columnEncoding IntegerArithmetic.encoding
    (src.andThen RawColumns.computes) (fun x c => MatrixCells.diagonal D (x.2, c))
    ((pairComputes (ctx.andThen q) col).andThen (MatrixCells.diagonalComputes D))
  exact AccessPrograms.map columnEncoding LP.rowEncoding RawColumns.computes
    (fun r q => (columns r).map (fun c => MatrixCells.diagonal D (q, c))) inner

def dimensionComputes : Computes (Source.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
    (fun r => (columns r).length) := RawColumns.computes.andThen (WireLists.lengthComputes columnEncoding)

def computesRaw (D : Source.Family s arity) :
    Computes (Source.inputEncoding (s := s) (arity := arity)) LP.encoding (raw D) := by
  let v := vertexCountComputes s 1 arity
  let e := edgeCountComputes s 1 arity
  let m := dimensionComputes (s := s) (arity := arity)
  let ve := (pairComputes v e).andThen AccessPrograms.unaryAdd
  let count := (pairComputes ve m).andThen AccessPrograms.unaryAdd
  let rowsVE := (pairComputes (vertexRowsComputes (s := s) (arity := arity))
    (edgeRowsComputes (s := s) (arity := arity))).andThen (WireLists.append LP.rowEncoding)
  let rows := (pairComputes rowsVE (zeroRowsComputes D)).andThen (WireLists.append LP.rowEncoding)
  let ones := v.andThen (WireLists.replicate IntegerArithmetic.encoding 1)
  let zeroCount := (pairComputes e m).andThen AccessPrograms.unaryAdd
  let zeros := zeroCount.andThen (WireLists.replicate IntegerArithmetic.encoding 0)
  let rhs := (pairComputes ones zeros).andThen (WireLists.append IntegerArithmetic.encoding)
  exact recode (pairComputes count (pairComputes m (pairComputes rows rhs))) id
    (fun _ => rfl) (fun _ => rfl)

def computes (D : Source.Family s arity) :
    Computes (Source.inputEncoding (s := s) (arity := arity)) LP.inputEncoding (value D) :=
  recode (computesRaw D) id (fun _ => rfl) (fun _ => rfl)

theorem primitive_bound (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) :
    primitiveCost (computes D).machine ((computes D).outputs r).steps
      (some (Turing.initList (computes D).machine.computer (Source.inputEncoding.encode r))) ≤
        (primitivePolynomial (computes D)).eval (Source.inputEncoding.encode r).length :=
  computes_primitive_cost (computes D) r

theorem output_bits (D : Source.Family s arity) (r : Source.Input (s := s) (arity := arity)) :
    (LP.inputEncoding.encode (value D r)).length ≤
      (computes D).outputBound.bound.eval (Source.inputEncoding.encode r).length :=
  (computes D).outputBound.length_le r

end
end Holant.LocalDrafts.Tractability.EOEvaluation.MatrixCompiler
