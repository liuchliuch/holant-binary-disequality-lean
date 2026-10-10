import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev actual : Machine := ChildPredicate.machine
abbrev Base := List (ℕ × ℕ) × (ℕ × List Graph.ParentRow)
def baseEncoding := pairEncoding EdgeSelect.edgeEncoding (pairEncoding UnaryBinary.unaryEncoding ParentRowEncoding.table)
def Valid (x : Base) : Prop := ∀ row∈x.2.2, ParentOpposite.Valid (x.1,row)
instance (x : Base) : Decidable (Valid x) := inferInstanceAs (Decidable (∀ row∈x.2.2, ParentOpposite.Valid (x.1,row)))
abbrev Input := {x : Base // Valid x}
def inputEncoding : Encoding Input Bool where
  encode x := baseEncoding.encode x.val
  decode bits := do
    let x ← baseEncoding.decode bits
    if h : Valid x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

def predicate (edges : List (ℕ × ℕ)) (target : ℕ) (row : Graph.ParentRow) : Bool :=
  if h : ParentOpposite.Valid (edges,row) then ChildPredicate.value (target,⟨(edges,row),h⟩) else false

def childrenFrom (edges : List (ℕ × ℕ)) (target : ℕ) : ℕ → List Graph.ParentRow → List ℕ
  | _,[] => []
  | i,row::rows => if predicate edges target row then i::childrenFrom edges target (i+1) rows
      else childrenFrom edges target (i+1) rows

def bits (ids : List ℕ) : List Bool := ids.flatMap childEntry
@[simp] theorem bits_nil : bits []=[] := rfl
@[simp] theorem bits_cons (i : ℕ) (ids : List ℕ) : bits (i::ids)=childEntry i++bits ids := rfl
@[simp] theorem childEntry_length (i : ℕ) : (childEntry i).length=2*i+2 := by simp [childEntry,Holant.Algebraic.frame_length]

theorem bits_encode (ids : List ℕ) : bits ids++[false]=framedListEncode UnaryBinary.unaryEncoding ids := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    simp only [bits_cons,List.append_assoc,framedListEncode]
    exact congrArg (fun tail => childEntry i++tail) ih

theorem children_bits_length (edges : List (ℕ × ℕ)) (target i : ℕ) (rows : List Graph.ParentRow) :
    (bits (childrenFrom edges target i rows)).length≤rows.length*(2*(i+rows.length)+2) := by
  induction rows generalizing i with
  | nil => simp [childrenFrom]
  | cons row rows ih =>
    have ht := ih (i+1)
    cases hp : predicate edges target row <;>
      simp only [childrenFrom,hp,Bool.false_eq_true,↓reduceIte,bits_cons,List.length_append,childEntry_length,List.length_cons]
    all_goals nlinarith

def value (x : Input) : List ℕ := childrenFrom x.val.1 x.val.2.1 0 x.val.2.2
abbrev outputEncoding := framedListEncoding UnaryBinary.unaryEncoding

theorem member_length (rows : List Graph.ParentRow) (row : Graph.ParentRow) (hr : row∈rows) :
    (ParentRowEncoding.row.encode row).length≤(framedListEncode ParentRowEncoding.row rows).length := by
  induction rows with
  | nil => simp at hr
  | cons r rows ih =>
    rcases List.mem_cons.mp hr with h|h
    · subst r
      simp only [framedListEncode,List.length_cons,List.length_append,Holant.Algebraic.frame_length]
      omega
    · have ht := ih h
      simp only [framedListEncode,List.length_cons,List.length_append,Holant.Algebraic.frame_length]
      omega

theorem input_word (x : Input) : inputEncoding.encode x =
    Holant.Algebraic.frame (ReachRound.encode x.val.1)++(Holant.Algebraic.frame (List.replicate x.val.2.1 true)++
      framedListEncode ParentRowEncoding.row x.val.2.2) := rfl

theorem input_bounds (x : Input) :
    (ReachRound.encode x.val.1).length≤(inputEncoding.encode x).length ∧
    x.val.2.1≤(inputEncoding.encode x).length ∧
    x.val.2.2.length≤(inputEncoding.encode x).length ∧
    ∀ row∈x.val.2.2, (ParentRowEncoding.row.encode row).length≤(inputEncoding.encode x).length := by
  have hl := framedListEncode_length_lower ParentRowEncoding.row x.val.2.2
  simp only [input_word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  refine ⟨by omega,by omega,by omega,?_⟩
  intro row hr
  have hm := member_length x.val.2.2 row hr
  omega

noncomputable def roundPolynomial : Polynomial ℕ := ChildPredicate.timePolynomial.comp (6*(Polynomial.X+1))+15*Polynomial.X+21
noncomputable def timePolynomial : Polynomial ℕ := Polynomial.X*roundPolynomial+7*Polynomial.X+2*(Polynomial.X+1)^2+12

theorem query_length (edges : List (ℕ × ℕ)) (target : ℕ) (row : Graph.ParentRow) (h : ParentOpposite.Valid (edges,row))
    (N : ℕ) (he : (ReachRound.encode edges).length≤N) (ht : target≤N) (hr : (ParentRowEncoding.row.encode row).length≤N) :
    (ChildPredicate.inputEncoding.encode (target,⟨(edges,row),h⟩)).length≤6*(N+1) := by
  change (queryWord (ReachRound.encode edges) (List.replicate target true) (ParentRowEncoding.row.encode row)).length≤_
  simp only [queryWord,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
