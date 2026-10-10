import Holant.Proofs.Algorithms.TransformRecognition.RationalCompiler


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicInputTable
open Holant Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
variable {n v d : ℕ}

def vertex (D : ArithmeticData d) (A : Bool → Bool → Poly v d)
    (table : (Fin n → Bool) → Poly v d) (x : Fin n → Bool) : Poly v d :=
  SparseTransform.total ((SparseTransform.allWords n).map (fun y =>
    mul D (SparseTransform.product D (List.ofFn (fun j => A (x j) (y j)))) (table y)))

def edge (D : ArithmeticData d) (U : Bool → Bool → Poly v d)
    (table : Bool → Bool → Poly v d) (a b : Bool) : Poly v d :=
  SparseTransform.total ([false,true].flatMap (fun i => [false,true].map (fun j =>
    mul D (mul D (U i a) (table i j)) (U j b))))

variable {K E : Type*} [Field K] [Algebra ℚ K] [Field E]
    (F : FixedField K d) (φ : K →+* E)
noncomputable section

theorem vertex_eval (A : Bool → Bool → Poly v d)
    (table : (Fin n → Bool) → Poly v d) (x : Fin n → Bool) (z : Fin v → E) :
    SparseEvaluation.evaluate F φ z (vertex F.toArithmeticData A table x) =
      Signature.coordinateAction (fun _ a b => SparseEvaluation.evaluate F φ z (A a b))
        (fun y => SparseEvaluation.evaluate F φ z (table y)) x := by
  simp [vertex,SparseTransform.sum_allWords,List.map_map,List.map_ofFn,List.prod_ofFn,
    Function.comp_def,Signature.coordinateAction]

theorem edge_eval (U : Bool → Bool → Poly v d) (table : Bool → Bool → Poly v d)
    (a b : Bool) (z : Fin v → E) :
    SparseEvaluation.evaluate F φ z (edge F.toArithmeticData U table a b) =
      Kernel.pullback (fun i j => SparseEvaluation.evaluate F φ z (table i j))
        (fun i j => SparseEvaluation.evaluate F φ z (U i j)) a b := by
  simp [edge,Kernel.pullback,Kernel.mul,Kernel.transpose,mul_add,add_mul,mul_assoc] <;> ring

/-- Binding an original input entry to a variable is substitution by a
proved equation, not a newly supplied common-field encoding. -/
theorem variable_vertex_eval (address : (Fin n → Bool) → Fin v)
    (A : Bool → Bool → Poly v d) (f : Signature E n) (z : Fin v → E)
    (hbind : ∀ y, z (address y)=f y) (x : Fin n → Bool) :
    SparseEvaluation.evaluate F φ z
      (vertex F.toArithmeticData A (fun y => SparseTransform.variableCode F.toArithmeticData (address y)) x) =
      Signature.coordinateAction (fun _ a b => SparseEvaluation.evaluate F φ z (A a b)) f x := by
  rw [vertex_eval]
  simp only [SparseEvaluation.variable_eval,hbind]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicInputTable
