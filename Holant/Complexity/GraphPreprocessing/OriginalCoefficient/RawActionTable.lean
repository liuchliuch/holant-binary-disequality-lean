import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTableRun
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionRow

/-! Complete original-ID action-table emission from raw graph bytes. The
machine counts the actual input vertices, queries each row, emits all literal
frames and preserves original vertex order, including an empty-table marker. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionTable
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {r : RawClosedNetwork // r.WellFormed s b arity}
def value (x : Input s b arity) := OriginalWordTable.rows RawActionRow.value x.val x.property
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) := CountsPackage.machine.compose (ParentTableLoop.machine (RawActionRow.machine s b arity))
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (framedListEncoding Frame.wordEncoding) value :=
  OriginalWordTable.computes (RawActionRow.computes s b arity)
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity) (framedListEncoding Frame.wordEncoding) value := (computes s b arity).inFP
@[simp] theorem value_length (x : Input s b arity) : (value x).length=x.val.vertices.length := by simp [value]
theorem get_row (x : Input s b arity) (v : Fin x.val.vertices.length) :
    (value x)[v.val]'(by simpa using v.isLt)=RawActionRow.value ⟨x,v⟩ := by simp [value,OriginalWordTable.rows]

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime (machine s b arity).computer (RawClosedNetwork.encoding.encode x.val)
      (some (Traversal.tableBits (value x)))
      ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length) := (computes s b arity).outputs x
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost (machine s b arity) (timed x).steps (some (initList (machine s b arity).computer (RawClosedNetwork.encoding.encode x.val))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

theorem list_length (xs : List (List Bool)) (B : ℕ) (h : ∀ row∈xs,row.length≤B) :
    (Traversal.tableBits xs).length≤xs.length*(2*B+2)+1 := by
  change (framedListEncode Frame.wordEncoding xs).length≤_
  induction xs with
  | nil => simp [framedListEncode]
  | cons row xs ih =>
    have hh := h row (by simp)
    have ht := ih (fun r hr => h r (by simp [hr]))
    simp only [framedListEncode,List.length_cons,List.length_append,Holant.Algebraic.frame_length]
    change 2*row.length+1+(framedListEncode Frame.wordEncoding xs).length+1≤(xs.length+1)*(2*B+2)+1
    nlinarith
theorem output_length (x : Input s b arity) :
    let N := (RawClosedNetwork.encoding.encode x.val).length
    let C := lengthBound s b arity
    (Traversal.tableBits (value x)).length≤N*(2*(8*C+6+N*(4*C+N+6))+2)+1 := by
  dsimp only
  have hb := list_length (value x) (8*lengthBound s b arity+6+(RawClosedNetwork.encoding.encode x.val).length*
      (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode x.val).length+6)) (by
    intro row hr
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
    exact RawActionRow.output_length ⟨x,v⟩)
  rw [value_length] at hb
  have hc := x.val.counts_le_encoded_length
  exact le_trans hb (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionTable
