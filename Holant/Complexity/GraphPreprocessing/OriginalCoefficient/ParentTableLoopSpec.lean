import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoopFinish
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackageInterface

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

def prefixWord (g : Graph) (n : ℕ) : List Bool :=
  (g.parentTable.take n).flatMap (fun row => entry (ParentRowEncoding.row.encode row))
@[simp] theorem prefix_zero (g : Graph) : prefixWord g 0=[] := rfl

theorem prefix_succ (g : Graph) (n : ℕ) (hn : n<g.vertices) :
    prefixWord g (n+1)=prefixWord g n++entry (ParentRowEncoding.row.encode (g.parentRow ⟨n,hn⟩)) := by
  have ht : n<g.parentTable.length := by simpa using hn
  have hr : g.parentTable[n]=g.parentRow ⟨n,hn⟩ := by simp [Graph.parentTable,List.get_eq_getElem]
  simp only [prefixWord,List.take_succ_eq_append_getElem ht,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,hr]

theorem framed_rows (rows : List Graph.ParentRow) :
    rows.flatMap (fun row => entry (ParentRowEncoding.row.encode row))++[false] =
      framedListEncode ParentRowEncoding.row rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.flatMap_cons,List.append_assoc,framedListEncode]
    exact congrArg (fun tail => entry (ParentRowEncoding.row.encode row)++tail) ih

theorem prefix_full (g : Graph) : prefixWord g g.vertices++[false]=ParentRowEncoding.table.encode g.parentTable := by
  have hl : g.parentTable.take g.vertices=g.parentTable := by rw [←g.parentTable_length]; exact List.take_length
  rw [prefixWord,hl,framed_rows]
  rfl

noncomputable def roundPolynomial (w : Computes (RawParentRow.inputEncoding s b arity) ParentRowEncoding.row RawParentRow.value) : Polynomial ℕ :=
  w.time.comp (3*(Polynomial.X+1))+2*w.outputBound.bound.comp (3*(Polynomial.X+1))+6*Polynomial.X+12
noncomputable def timePolynomial (w : Computes (RawParentRow.inputEncoding s b arity) ParentRowEncoding.row RawParentRow.value) : Polynomial ℕ :=
  Polynomial.X*roundPolynomial w+6*Polynomial.X+9

theorem round_bound (w : Computes (RawParentRow.inputEncoding s b arity) ParentRowEncoding.row RawParentRow.value)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length) :
    (w.outputs ⟨⟨r,h⟩,v⟩).steps+4*(RawClosedNetwork.encoding.encode r).length+2*v.val+
      2*(ParentRowEncoding.row.encode (RawParentRow.value ⟨⟨r,h⟩,v⟩)).length+12 ≤
        (roundPolynomial w).eval (RawClosedNetwork.encoding.encode r).length := by
  let x : RawParentRow.Input s b arity := ⟨⟨r,h⟩,v⟩
  have hi : ((RawParentRow.inputEncoding s b arity).encode x).length≤
      3*((RawClosedNetwork.encoding.encode r).length+1) := RawRootReach.input_length_le_original x
  have ht := natPolynomial_eval_mono w.time hi
  have hs := (w.outputs x).steps_le_m
  have ho := w.outputBound.length_le x
  have hm := natPolynomial_eval_mono w.outputBound.bound hi
  have hc := r.counts_le_encoded_length
  have hv := v.isLt
  simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
    Polynomial.eval_comp,Polynomial.eval_one]
  change (w.outputs x).steps+4*(RawClosedNetwork.encoding.encode r).length+2*v.val+
    2*(ParentRowEncoding.row.encode (RawParentRow.value x)).length+12≤_
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
