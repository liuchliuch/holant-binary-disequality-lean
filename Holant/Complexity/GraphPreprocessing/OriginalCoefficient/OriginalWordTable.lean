import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoopInterface
import Holant.Complexity.GraphPreprocessing.FrameMachine

/-! Generic word-row specification for the existing physical original-vertex
table loop. The row provider may emit traversal actions; the executed original
vertex count, descending counter, framing, original order and cleanup are the
same actual finite program already used for canonical parent tables. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTable
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

def rows (f : RawRootReach.Input s b arity → List Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) :=
  (List.finRange r.vertices.length).map (fun v => f ⟨⟨r,h⟩,v⟩)
@[simp] theorem rows_length (f : RawRootReach.Input s b arity → List Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    (rows f r h).length=r.vertices.length := by simp [rows]
def prefixWord (f : RawRootReach.Input s b arity → List Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) (n : ℕ) :=
  ((rows f r h).take n).flatMap ParentTableLoop.entry
@[simp] theorem prefix_zero (f : RawRootReach.Input s b arity → List Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    prefixWord f r h 0=[] := rfl
theorem prefix_succ (f : RawRootReach.Input s b arity → List Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (n : ℕ) (hn : n<r.vertices.length) :
    prefixWord f r h (n+1)=prefixWord f r h n++ParentTableLoop.entry (f ⟨⟨r,h⟩,⟨n,hn⟩⟩) := by
  have ht : n<(rows f r h).length := by simpa using hn
  have hr : (rows f r h)[n]=f ⟨⟨r,h⟩,⟨n,hn⟩⟩ := by simp [rows]
  simp only [prefixWord,List.take_succ_eq_append_getElem ht,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,hr]
theorem framed_rows (xs : List (List Bool)) : xs.flatMap ParentTableLoop.entry++[false]=framedListEncode Frame.wordEncoding xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.append_assoc,framedListEncode]
    exact congrArg (fun tail => ParentTableLoop.entry x++tail) ih
theorem prefix_full (f : RawRootReach.Input s b arity → List Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    prefixWord f r h r.vertices.length++[false]=framedListEncode Frame.wordEncoding (rows f r h) := by
  have hl : (rows f r h).take r.vertices.length=rows f r h := by rw [←rows_length f r h]; exact List.take_length
  rw [prefixWord,hl,framed_rows]

variable {f : RawRootReach.Input s b arity → List Bool}
noncomputable def roundPolynomial (w : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding f) : Polynomial ℕ :=
  w.time.comp (3*(Polynomial.X+1))+2*w.outputBound.bound.comp (3*(Polynomial.X+1))+6*Polynomial.X+12
noncomputable def timePolynomial (w : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding f) : Polynomial ℕ :=
  Polynomial.X*roundPolynomial w+6*Polynomial.X+9
theorem round_bound (w : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding f)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length) :
    (w.outputs ⟨⟨r,h⟩,v⟩).steps+4*(RawClosedNetwork.encoding.encode r).length+2*v.val+
      2*(f ⟨⟨r,h⟩,v⟩).length+12≤(roundPolynomial w).eval (RawClosedNetwork.encoding.encode r).length := by
  let x : RawRootReach.Input s b arity := ⟨⟨r,h⟩,v⟩
  have hi := RawRootReach.input_length_le_original x
  have ht := natPolynomial_eval_mono w.time hi
  have hs := (w.outputs x).steps_le_m
  have ho := w.outputBound.length_le x
  have hm := natPolynomial_eval_mono w.outputBound.bound hi
  have hc := r.counts_le_encoded_length
  have hv := v.isLt
  change (f x).length≤_ at ho
  simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_one]
  change (w.outputs x).steps+4*(RawClosedNetwork.encoding.encode r).length+2*v.val+2*(f x).length+12≤_
  dsimp only [x] at *
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTable
