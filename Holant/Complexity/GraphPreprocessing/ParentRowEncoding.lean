import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Holant.OneHot.Computable.Tables

/-! The physical table contract for the original-graph compiler. Rows retain
original vertex order, least-component ID, first-success rank, and the original
edge ID plus child-end orientation. This is a codec, not a claim that the entire
parent-table producer machine has been completed. -/
namespace Holant.Complexity.GraphPreprocessing.ParentRowEncoding
open Computability Holant.OneHot.Computable

def orientation : Encoding Bool Bool where
  encode z := [z]
  decode
    | [z] => some z
    | _ => none
  decode_encode _ := rfl

def endpoint : Encoding (ℕ × Bool) Bool :=
  framedProductEncoding UnaryBinary.unaryEncoding orientation

def parent : Encoding (Option (ℕ × Bool)) Bool where
  encode
    | none => [false]
    | some e => true :: endpoint.encode e
  decode
    | [] => none
    | false :: rest => if rest = [] then some none else none
    | true :: rest => (endpoint.decode rest).map some
  decode_encode e := by cases e <;> simp

def tuple : Encoding (ℕ × (ℕ × Option (ℕ × Bool))) Bool :=
  framedProductEncoding UnaryBinary.unaryEncoding (framedProductEncoding UnaryBinary.unaryEncoding parent)

def row : Encoding Graph.ParentRow Bool where
  encode r := tuple.encode (r.component,(r.depth,r.parent))
  decode bits := (tuple.decode bits).map fun p => ⟨p.1,p.2.1,p.2.2⟩
  decode_encode r := by cases r; simp

def table : Encoding (List Graph.ParentRow) Bool := framedListEncoding row

@[simp] theorem parent_none : parent.encode none = [false] := rfl
@[simp] theorem parent_some (e : ℕ) (z : Bool) :
    parent.encode (some (e,z)) = true :: (Holant.Algebraic.frame (List.replicate e true) ++ [z]) := rfl

/-- Literal on-tape row layout; all integer fields are bounded physical unary words. -/
theorem row_word (r : Graph.ParentRow) :
    row.encode r = Holant.Algebraic.frame (List.replicate r.component true) ++
      (Holant.Algebraic.frame (List.replicate r.depth true) ++ parent.encode r.parent) := rfl

/-- Existing framed-list indexing can select every original vertex row. -/
theorem table_word (rows : List Graph.ParentRow) : table.encode rows = framedListEncode row rows := rfl

@[simp] theorem row_roundtrip (r : Graph.ParentRow) : row.decode (row.encode r) = some r := row.decode_encode r
@[simp] theorem table_roundtrip (rows : List Graph.ParentRow) : table.decode (table.encode rows) = some rows := table.decode_encode rows

/-- No vertex reordering, quotient enumeration, or port renumbering is hidden in the table contract. -/
theorem original_row (g : Graph) (v : g.Vertex) :
    g.parentTable.get (Fin.cast (g.parentTable_length).symm v) = g.parentRow v := by
  simp [Graph.parentTable, List.get_eq_getElem]
  rfl

/-- The physical component field is the original deterministic least root. -/
theorem component_field (g : Graph) (v : g.Vertex) :
    (g.parentTable.get (Fin.cast (g.parentTable_length).symm v)).component = (g.label v).val := by
  rw [original_row]
  rfl

/-- The physical depth is the existing compiler's exact first-success rank. -/
theorem depth_field (g : Graph) (v : g.Vertex) :
    (g.parentTable.get (Fin.cast (g.parentTable_length).symm v)).depth =
      g.depth (g.label v) (g.labelledVertex v) := by
  rw [original_row]
  rfl

/-- A nonroot retains the actual first matching original edge/end, not an arbitrary spanning edge. -/
theorem parent_field (g : Graph) (v : g.Vertex) :
    (g.parentTable.get (Fin.cast (g.parentTable_length).symm v)).parent = (g.parentRow v).parent := by
  rw [original_row]

end Holant.Complexity.GraphPreprocessing.ParentRowEncoding
