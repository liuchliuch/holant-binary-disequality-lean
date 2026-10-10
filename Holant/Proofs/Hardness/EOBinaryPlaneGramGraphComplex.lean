import Holant.Proofs.Hardness.EOBinaryPlaneGramGraph
import Holant.Proofs.Hardness.EOBinaryPlaneFlat

/-! Complex specialization of the actual two-label Gram graph. The second
supplied label is the pointwise conjugate of the first; this identity supplies
no independent access to that conjugate label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGramGraphComplex
open Holant
open scoped BigOperators
namespace N
export EOBinaryPlaneGramGraph (output network palette template valid denote template_denote)
end N
namespace G
export EOBinaryPlaneGram (table cross leftNorm)
end G
namespace F
export EOBinaryPlaneFlat (norm_product)
end F


def conjugate (f : Signature ℂ 2) : Signature ℂ 2 := fun x=>star (f x)

def matrix (a b c d : ℂ) : Signature ℂ 2 := fun x=>
  if x 0 then (if x 1 then d else c) else if x 1 then b else a

theorem output_star (f : Signature ℂ 2) (x : Fin 2→Bool) :
    N.output f (conjugate f) x=
      (Complex.normSq (∑z : Bool,f ![x 0,z]*star (f ![x 1,z])) : ℂ) := by
  rw [←F.norm_product]
  simp only [N.output,conjugate,Fintype.sum_bool,star_add,star_mul,star_star]
  ring

private theorem diagonal_norm (a b : ℂ) :
    Complex.normSq (b*star b+a*star a)=G.leftNorm a b^2 := by
  rw [F.norm_product,F.norm_product,←Complex.ofReal_add,Complex.normSq_ofReal]
  simp [G.leftNorm,add_comm,pow_two]

private theorem reverse_norm (a b c d : ℂ) :
    Complex.normSq (d*star b+c*star a)=Complex.normSq (G.cross a b c d) := by
  have h : d*star b+c*star a=star (G.cross a b c d) := by
    simp only [G.cross,star_add,star_mul,star_star]
    ring
  rw [h,Complex.star_def,Complex.normSq_conj]

/-- The graph's exact binary output is the previously analysed positive real
Gram table embedded in ℂ, without a projective scale. -/
theorem output_matrix (a b c d : ℂ) :
    N.output (matrix a b c d) (conjugate (matrix a b c d))=
      fun x=>(G.table a b c d x : ℂ) := by
  funext x
  rw [output_star]
  apply congrArg Complex.ofReal
  cases h0 : x 0 <;> cases h1 : x 1
  · simpa only [Fintype.sum_bool,matrix,h0,h1,Bool.false_eq_true,ite_false,ite_true,
      G.table,Matrix.cons_val_zero,Matrix.cons_val_one] using diagonal_norm a b
  · simp [Fintype.sum_bool,matrix,h0,h1,G.table,G.cross,add_comm]
  · simpa only [Fintype.sum_bool,matrix,h0,h1,Bool.false_eq_true,ite_false,ite_true,
      G.table,Matrix.cons_val_zero,Matrix.cons_val_one] using reverse_norm a b c d
  · simpa only [Fintype.sum_bool,matrix,h0,h1,Bool.false_eq_true,ite_false,ite_true,
      G.table,Matrix.cons_val_zero,Matrix.cons_val_one] using diagonal_norm c d

theorem graph_gram (a b c d : ℂ) :
    (N.network (matrix a b c d) (conjugate (matrix a b c d))).denote=
      EOBinaryPlaneCore.lift (fun x=>(G.table a b c d x : ℂ)) := by
  rw [N.denote,output_matrix]

theorem template_gram (a b c d : ℂ) :
    (N.template.network N.valid (N.palette (matrix a b c d) (conjugate (matrix a b c d)))
      (fun _ : Fin 1=>Signature.disequality)).denote=
      EOBinaryPlaneCore.lift (fun x=>(G.table a b c d x : ℂ)) := by
  rw [N.template_denote,output_matrix]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGramGraphComplex
