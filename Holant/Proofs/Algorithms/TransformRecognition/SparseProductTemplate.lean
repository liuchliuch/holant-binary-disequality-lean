import Holant.Proofs.Algorithms.TransformRecognition.SparseEvaluation
import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Templates


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SparseProductTemplate
open Holant Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
variable {n v d : ℕ}

/-- Repeated edge constraints are checked again; they are never XOR-cancelled. -/
def edgeCheck (e : Edge n) (x : Fin n → Bool) : Bool :=
  if e.2 then x e.1.1 == x e.1.2 else !(x e.1.1 == x e.1.2)
def holdsCheck (edges : List (Edge n)) (x : Fin n → Bool) : Bool :=
  edges.all (fun e => edgeCheck e x)

theorem edgeCheck_iff (e : Edge n) (x : Fin n → Bool) :
    edgeCheck e x = true ↔ edgeHolds e x := by
  obtain ⟨⟨i,j⟩,b⟩ := e
  cases b <;> simp [edgeCheck,edgeHolds]

theorem holdsCheck_iff (edges : List (Edge n)) (x : Fin n → Bool) :
    holdsCheck edges x = true ↔ holds edges.toFinset x := by
  simp [holdsCheck,List.all_eq_true,edgeCheck_iff,holds]

/-- Indices supplied here are the compiler's variable address map, not
values of a Product witness. The family compiler allocates disjoint blocks. -/
def entry (D : ArithmeticData d) (edges : List (Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) : Poly v d :=
  if holdsCheck edges x then
    mul D (SparseTransform.variableCode D (address none))
      (SparseTransform.product D (List.ofFn (fun j =>
        SparseTransform.variableCode D (address (some (j,x j))))))
  else []

def row (D : ArithmeticData d) (A : Bool → Bool → Poly v d)
    (table : SparseTransform.Table n d) (edges : List (Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) : Poly v d :=
  sub (SparseTransform.vertex D A table x) (entry D edges address x)

/-- Emit every local truth-table equation, including the single nullary row. -/
def rows (D : ArithmeticData d) (A : Bool → Bool → Poly v d)
    (table : SparseTransform.Table n d) (edges : List (Edge n))
    (address : Parameter n → Fin v) : List (Poly v d) :=
  (SparseTransform.allWords n).map (row D A table edges address)

theorem rows_length (D : ArithmeticData d) (A : Bool → Bool → Poly v d)
    (table : SparseTransform.Table n d) (edges : List (Edge n))
    (address : Parameter n → Fin v) : (rows D A table edges address).length = 2^n := by
  simp [rows,SparseTransform.allWords_length]

variable {K E : Type*} [Field K] [Algebra ℚ K] [Field E]
  (F : FixedField K d) (φ : K →+* E)
noncomputable section

theorem entry_eval (edges : List (Edge n)) (address : Parameter n → Fin v)
    (z : Fin v → E) (x : Fin n → Bool) :
    SparseEvaluation.evaluate F φ z (entry F.toArithmeticData edges address x) =
      evaluate edges.toFinset (fun p => z (address p)) x := by
  rw [entry,entry_formula]
  by_cases h : holdsCheck edges x = true
  · have hs := (holdsCheck_iff edges x).mp h
    simp [h,hs,List.map_ofFn,List.prod_ofFn]
  · have hs : ¬ holds edges.toFinset x := fun hs => h ((holdsCheck_iff edges x).mpr hs)
    simp [h,hs,SparseEvaluation.evaluate]

theorem row_eval (A : Bool → Bool → Poly v d)
    (table : SparseTransform.Table n d) (edges : List (Edge n))
    (address : Parameter n → Fin v) (z : Fin v → E) (x : Fin n → Bool) :
    SparseEvaluation.evaluate F φ z (row F.toArithmeticData A table edges address x) =
      Signature.coordinateAction (fun _ a b => SparseEvaluation.evaluate F φ z (A a b))
        (SparseEvaluation.signature F φ table) x -
      evaluate edges.toFinset (fun p => z (address p)) x := by
  rw [row,SparseEvaluation.sub_eval,SparseEvaluation.vertex_eval,entry_eval]

theorem rows_zero_iff (A : Bool → Bool → Poly v d)
    (table : SparseTransform.Table n d) (edges : List (Edge n))
    (address : Parameter n → Fin v) (z : Fin v → E) :
    (∀ p ∈ rows F.toArithmeticData A table edges address,
      SparseEvaluation.evaluate F φ z p=0) ↔
    Signature.coordinateAction (fun _ a b => SparseEvaluation.evaluate F φ z (A a b))
      (SparseEvaluation.signature F φ table) =
        evaluate edges.toFinset (fun p => z (address p)) := by
  constructor
  · intro h
    funext x
    have hx := h _ (List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩)
    rw [row_eval] at hx
    exact sub_eq_zero.mp hx
  · intro h p hp
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
    rw [row_eval]
    exact sub_eq_zero.mpr (congrFun h x)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SparseProductTemplate
