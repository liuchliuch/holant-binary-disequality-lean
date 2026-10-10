import Holant.Proofs.Tractability.EOEvaluation.Size
import Holant.Proofs.Tractability.EOEvaluation.PairingTemplates
import Holant.Proofs.Traversal.RationalLP.Parsing


namespace Holant.LocalDrafts.Tractability.EOEvaluation.RawColumns
open Computability Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open AffineMachine LocalAffineMachine.Relabel
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Column := ℕ × (RawVertex × ℕ)
def columnEncoding := pairEncoding UnaryBinary.unaryEncoding
  (pairEncoding RawClosedNetwork.vertexEncoding encodingNatBool)
def columnsEncoding := framedListEncoding columnEncoding
abbrev Vertex := ℕ × RawVertex
def vertexEncoding := pairEncoding UnaryBinary.unaryEncoding RawClosedNetwork.vertexEncoding
def localCount (i : Fin s) := Fintype.card (Word (arity i.val))
def localWord (i : Fin s) (k : Fin (localCount (arity := arity) i)) : Word (arity i.val) :=
  (Fintype.equivFin (Word (arity i.val))).symm k

def vertexColumns (x : Vertex) : List Column :=
  FiniteDispatch.select (fun x : Vertex => x.2.1)
    (fun x i => (List.finRange (localCount (arity := arity) i)).map (fun k => (x.1, x.2, k.val)))
    (fun _ => []) (List.finRange s) x

theorem vertexColumns_valid (x : Vertex) (h : x.2.1 < s) :
    vertexColumns (s := s) (arity := arity) x =
      (List.finRange (localCount (arity := arity) ⟨x.2.1, h⟩)).map (fun k => (x.1, x.2, k.val)) :=
  FiniteDispatch.select_at _ _ _ _ _ (by simp) x rfl

def vertexColumnsComputes : Computes vertexEncoding columnsEncoding (vertexColumns (s := s) (arity := arity)) := by
  let v := Wiring.firstComputes UnaryBinary.unaryEncoding RawClosedNetwork.vertexEncoding
  let row := Wiring.secondComputes UnaryBinary.unaryEncoding RawClosedNetwork.vertexEncoding
  let label := row.andThen (recode (Wiring.firstComputes encodingNatBool
    (framedListEncoding RawClosedNetwork.endpointEncoding)) id (fun _ => rfl) (fun _ => rfl))
  let branch (i : Fin s) := fixedListComputes vertexEncoding columnEncoding
    (fun x (k : Fin (localCount (arity := arity) i)) => (x.1, x.2, k.val))
    (fun k => pairComputes v (pairComputes row (constantComputes vertexEncoding encodingNatBool k.val)))
    (List.finRange (localCount (arity := arity) i))
  exact FiniteDispatch.computes vertexEncoding columnsEncoding _ _ _ label branch
    (constantComputes vertexEncoding columnsEncoding []) (List.finRange s)

def columns (r : Source.Input (s := s) (arity := arity)) : List Column :=
  (List.range r.val.vertices.length).flatMap (fun v =>
    vertexColumns (s := s) (arity := arity) (v, r.val.vertices.getD v (0, [])))

def indexedEncoding := pairEncoding (Source.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
def vertexCell : Computes (indexedEncoding (s := s) (arity := arity)) columnsEncoding
    (fun x => vertexColumns (s := s) (arity := arity) (x.2, x.1.val.vertices.getD x.2 (0, []))) := by
  let src := Wiring.firstComputes (Source.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  let v := Wiring.secondComputes (Source.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding
  let row := AccessPrograms.get RawClosedNetwork.vertexEncoding (0, [])
    (src.andThen (rowsComputes s 1 arity)) v
  exact (pairComputes v row).andThen vertexColumnsComputes

def computes : Computes (Source.inputEncoding (s := s) (arity := arity)) columnsEncoding columns :=
  congrComputes ((WireLists.tabulate Source.inputEncoding columnsEncoding
    (fun r => r.val.vertices.length) (vertexCountComputes s 1 arity)
    (fun r v => vertexColumns (s := s) (arity := arity) (v, r.val.vertices.getD v (0, [])))
    vertexCell).andThen (WireLists.flatten columnEncoding))
      (fun r => by simp only [columns, List.flatMap_def, Function.comp_apply])

theorem length_eq (r : Source.Input (s := s) (arity := arity)) :
    (columns r).length = Fintype.card (Source.Coordinate r) := by
  rw [Source.coordinate_count]
  simp only [columns, List.length_flatMap]
  rw [DensePrograms.range_map, List.sum_ofFn]
  apply Finset.sum_congr rfl; intro v _
  rw [List.getD_eq_getElem _ _ v.isLt, vertexColumns_valid _ (r.property.1 v).1]
  simp [localCount, Fintype.card_fun]

theorem primitive_bound (r : Source.Input (s := s) (arity := arity)) :
    primitiveCost (computes (s := s) (arity := arity)).machine
      ((computes (s := s) (arity := arity)).outputs r).steps
      (some (Turing.initList (computes (s := s) (arity := arity)).machine.computer
        ((Source.inputEncoding (s := s) (arity := arity)).encode r))) ≤
      (primitivePolynomial (computes (s := s) (arity := arity))).eval
        ((Source.inputEncoding (s := s) (arity := arity)).encode r).length :=
  computes_primitive_cost (computes (s := s) (arity := arity)) r

end
end Holant.LocalDrafts.Tractability.EOEvaluation.RawColumns
