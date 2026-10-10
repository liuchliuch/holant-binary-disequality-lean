import Holant.Proofs.Algorithms.TransformRecognition.SparseTransform


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SparseEvaluation
open Holant Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open SparseTransform
variable {K E : Type*} [Field K] [Algebra ℚ K] [Field E]
  {v d q n : ℕ} (F : FixedField K d) (φ : K →+* E)
noncomputable section

def evaluate (z : Fin v → E) (p : Poly v d) : E := eval₂ φ z (denote F p)

@[simp] theorem constant_eval (z : Fin v → E) (c : Coefficient d) :
    evaluate F φ z (constant c) = φ (F.decode c) := by
  simp [evaluate]
@[simp] theorem variable_eval (z : Fin v → E) (j : Fin v) :
    evaluate F φ z (variableCode F.toArithmeticData j) = z j := by
  simp [evaluate]
@[simp] theorem add_eval (z : Fin v → E) (p r : Poly v d) :
    evaluate F φ z (add p r) = evaluate F φ z p + evaluate F φ z r := by
  simp [evaluate]
@[simp] theorem neg_eval (z : Fin v → E) (p : Poly v d) :
    evaluate F φ z (neg p) = -evaluate F φ z p := by simp [evaluate]
@[simp] theorem sub_eval (z : Fin v → E) (p r : Poly v d) :
    evaluate F φ z (sub p r) = evaluate F φ z p - evaluate F φ z r := by
  simp [evaluate]
@[simp] theorem mul_eval (z : Fin v → E) (p r : Poly v d) :
    evaluate F φ z (mul F.toArithmeticData p r) =
      evaluate F φ z p * evaluate F φ z r := by simp [evaluate]
@[simp] theorem one_eval (z : Fin v → E) :
    evaluate F φ z (one F.toArithmeticData) = 1 := by simp [evaluate]
@[simp] theorem total_eval (z : Fin v → E) (ps : List (Poly v d)) :
    evaluate F φ z (total ps) = (ps.map (evaluate F φ z)).sum := by
  induction ps with
  | nil => simp [evaluate,total]
  | cons p ps ih =>
    change evaluate F φ z (add p (total ps)) = _
    simp only [add_eval,List.map_cons,List.sum_cons,ih]
@[simp] theorem product_eval (z : Fin v → E) (ps : List (Poly v d)) :
    evaluate F φ z (product F.toArithmeticData ps) =
      (ps.map (evaluate F φ z)).prod := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    change evaluate F φ z (mul F.toArithmeticData p (product F.toArithmeticData ps)) = _
    simp only [mul_eval,List.map_cons,List.prod_cons,ih]

@[simp] theorem matrix_eval (z : Fin (5+q) → E) (a b : Bool) :
    evaluate F φ z (matrix F.toArithmeticData q a b) =
      SymbolicTransform.matrix (point z) a b := by
  simp [matrix,SymbolicTransform.matrix,point]
@[simp] theorem inverse_eval (z : Fin (5+q) → E) (a b : Bool) :
    evaluate F φ z (inverse F.toArithmeticData q a b) =
      SymbolicTransform.inverse (point z) a b := by
  cases a <;> cases b <;>
    simp [inverse,matrix,SymbolicTransform.inverse,SymbolicTransform.adjugate,
      SymbolicTransform.matrix,SymbolicTransform.index,point]
@[simp] theorem guard_eval (z : Fin (5+q) → E) :
    evaluate F φ z (guard F.toArithmeticData q) =
      z (Fin.castAdd q 4) * SymbolicTransform.determinant
        (SymbolicTransform.matrix (point z)) - 1 := by
  simp [SparseTransform.guard,matrix,SymbolicTransform.determinant,SymbolicTransform.matrix,point]

def signature (table : Table n d) : Signature E n :=
  fun y => (table.map (fun row => if y=row.1 then φ (F.decode row.2) else 0)).sum

@[simp] theorem signature_dense (f : (Fin n → Bool) → Coefficient d) :
    signature F φ (denseTable f) = fun x => φ (F.decode (f x)) := by
  funext x
  simp [signature,denseTable,List.map_map,sum_allWords,Function.comp_def]

theorem vertex_eval (A : Bool → Bool → Poly v d) (table : Table n d)
    (z : Fin v → E) (x : Fin n → Bool) :
    evaluate F φ z (vertex F.toArithmeticData A table x) =
      Signature.coordinateAction (fun _ a b => evaluate F φ z (A a b))
        (signature F φ table) x := by
  induction table with
  | nil => simp [vertex,total,evaluate,signature,Signature.coordinateAction]
  | cons row rows ih =>
    have hs : signature F φ (row::rows) =
        (fun y => if y=row.1 then φ (F.decode row.2) else 0) + signature F φ rows := by
      funext y; simp [signature]
    have ht : vertex F.toArithmeticData A (row::rows) x =
        add (mul F.toArithmeticData
          (product F.toArithmeticData (List.ofFn (fun j => A (x j) (row.1 j))))
          (constant row.2)) (vertex F.toArithmeticData A rows x) := rfl
    rw [ht,add_eval,ih,hs,Signature.coordinateAction_add]
    congr 1
    simp [List.map_ofFn,List.prod_ofFn,Signature.coordinateAction,
      Finset.mul_sum,Finset.sum_mul]

theorem inverse_vertex_eval (table : Table n d) (z : Fin (5+q) → E)
    (x : Fin n → Bool) :
    evaluate F φ z (vertex F.toArithmeticData (inverse F.toArithmeticData q) table x) =
      Signature.coordinateAction (fun _ => SymbolicTransform.inverse (point z))
        (signature F φ table) x := by
  rw [vertex_eval]
  simp only [inverse_eval]

theorem edge_eval (U : Bool → Bool → Poly v d)
    (E₀ : Bool → Bool → Coefficient d) (z : Fin v → E) (a b : Bool) :
    evaluate F φ z (edge F.toArithmeticData U E₀ a b) =
      Kernel.pullback (fun i j => φ (F.decode (E₀ i j)))
        (fun i j => evaluate F φ z (U i j)) a b := by
  simp [edge,Kernel.pullback,Kernel.mul,Kernel.transpose,
    mul_add,add_mul,mul_assoc] <;> ring

theorem affineEquation_eval (A : Bool → Bool → Poly v d) (table : Table n d)
    (x : Fin n → Bool) (scale : Fin v) (phase : Coefficient d) (z : Fin v → E) :
    evaluate F φ z (affineEquation F.toArithmeticData A table x scale phase) =
      Signature.coordinateAction (fun _ a b => evaluate F φ z (A a b))
        (signature F φ table) x - z scale * φ (F.decode phase) := by
  rw [affineEquation,sub_eval,mul_eval,vertex_eval]
  simp

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SparseEvaluation
