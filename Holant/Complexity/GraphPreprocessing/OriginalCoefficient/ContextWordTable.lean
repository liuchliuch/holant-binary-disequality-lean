import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTable

/-! The actual original-vertex table loop, with an arbitrary encoded context.
Its count is computed by a real provider. In particular an input cut edge stays
on the tape and is copied into every row query. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextWordTable
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {A : Type} (ea : Encoding A Bool) (size : A → ℕ)
def queryEncoding := sigmaEncoding ea (fun x => OccurrenceLabel.unaryPortEncoding (size x))
def rows (f : (Σ x : A, Fin (size x)) → List Bool) (x : A) :=
  (List.finRange (size x)).map (fun v => f ⟨x,v⟩)
@[simp] theorem rows_length (f : (Σ x : A, Fin (size x)) → List Bool) (x : A) :
    (rows size f x).length=size x := by simp [rows]
def prefixWord (f : (Σ x : A, Fin (size x)) → List Bool) (x : A) (n : ℕ) :=
  ((rows size f x).take n).flatMap ParentTableLoop.entry
@[simp] theorem prefix_zero (f : (Σ x : A, Fin (size x)) → List Bool) (x : A) : prefixWord size f x 0=[] := rfl
theorem prefix_succ (f : (Σ x : A, Fin (size x)) → List Bool) (x : A) (n : ℕ) (hn : n<size x) :
    prefixWord size f x (n+1)=prefixWord size f x n++ParentTableLoop.entry (f ⟨x,⟨n,hn⟩⟩) := by
  have ht : n<(rows size f x).length := by simpa using hn
  have hr : (rows size f x)[n]=f ⟨x,⟨n,hn⟩⟩ := by simp [rows]
  simp only [prefixWord,List.take_succ_eq_append_getElem ht,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,hr]
theorem prefix_full (f : (Σ x : A, Fin (size x)) → List Bool) (x : A) :
    prefixWord size f x (size x)++[false]=framedListEncode Frame.wordEncoding (rows size f x) := by
  have hl : (rows size f x).take (size x)=rows size f x := by rw [←rows_length size f x]; exact List.take_length
  rw [prefixWord,hl,OriginalWordTable.framed_rows]

def packageEncoding : Encoding A Bool where
  encode x := (pairEncoding ea (pairEncoding UnaryBinary.unaryEncoding Frame.wordEncoding)).encode (x,size x,[])
  decode bits := do
    let (x,n,tail) ← (pairEncoding ea (pairEncoding UnaryBinary.unaryEncoding Frame.wordEncoding)).decode bits
    if n=size x ∧ tail=[] then some x else none
  decode_encode x := by
    rw [(pairEncoding ea (pairEncoding UnaryBinary.unaryEncoding Frame.wordEncoding)).decode_encode]
    simp

theorem raw_length_le_package (x : A) : (ea.encode x).length≤((packageEncoding ea size).encode x).length := by
  change (ea.encode x).length≤(Holant.Algebraic.frame (ea.encode x)++(Holant.Algebraic.frame (List.replicate (size x) true)++[])).length
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate,List.length_nil]
  omega

variable {ea size} {f : (Σ x : A, Fin (size x)) → List Bool}
noncomputable def roundPolynomial (w : Computes (queryEncoding ea size) Frame.wordEncoding f) : Polynomial ℕ :=
  w.time.comp (3*(Polynomial.X+1))+2*w.outputBound.bound.comp (3*(Polynomial.X+1))+6*Polynomial.X+12
noncomputable def timePolynomial (w : Computes (queryEncoding ea size) Frame.wordEncoding f) : Polynomial ℕ :=
  Polynomial.X*roundPolynomial w+6*Polynomial.X+9
theorem query_length (hsize : ∀x,size x≤(ea.encode x).length) (x : A) (v : Fin (size x)) :
    ((queryEncoding ea size).encode ⟨x,v⟩).length≤3*((ea.encode x).length+1) := by
  have hv := v.isLt
  have hs := hsize x
  change (Holant.Algebraic.frame (ea.encode x)++List.replicate v.val true).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

theorem round_bound (hsize : ∀x,size x≤(ea.encode x).length)
    (w : Computes (queryEncoding ea size) Frame.wordEncoding f) (x : A) (v : Fin (size x)) :
    (w.outputs ⟨x,v⟩).steps+4*(ea.encode x).length+2*v.val+2*(f ⟨x,v⟩).length+12≤(roundPolynomial w).eval (ea.encode x).length := by
  have hi := query_length hsize x v
  have ht := natPolynomial_eval_mono w.time hi
  have hs := (w.outputs ⟨x,v⟩).steps_le_m
  have ho := w.outputBound.length_le ⟨x,v⟩
  have hm := natPolynomial_eval_mono w.outputBound.bound hi
  have hc := hsize x
  have hv := v.isLt
  change (f ⟨x,v⟩).length≤_ at ho
  simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_one]
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextWordTable
