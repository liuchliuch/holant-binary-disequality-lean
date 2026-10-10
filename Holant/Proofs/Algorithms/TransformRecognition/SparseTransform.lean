import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.Sparse
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicTransform


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SparseTransform
open Holant Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
variable {v d q n : ℕ}

def constant (c : Coefficient d) : Poly v d := [(0,c)]
def variableCode (D : ArithmeticData d) (j : Fin v) : Poly v d :=
  [(fun i => if i=j then 1 else 0,D.unitCode)]
def total (ps : List (Poly v d)) : Poly v d := ps.flatten
def product (D : ArithmeticData d) (ps : List (Poly v d)) : Poly v d :=
  ps.foldr (mul D) (one D)

def matrix (D : ArithmeticData d) (q : ℕ) (a b : Bool) : Poly (5+q) d :=
  variableCode D (Fin.castAdd q (SymbolicTransform.index a b))
def inverse (D : ArithmeticData d) (q : ℕ) (a b : Bool) : Poly (5+q) d :=
  mul D (variableCode D (Fin.castAdd q 4))
    (if a=b then matrix D q (!a) (!b) else neg (matrix D q a b))
def guard (D : ArithmeticData d) (q : ℕ) : Poly (5+q) d :=
  sub (mul D (variableCode D (Fin.castAdd q 4))
    (sub (mul D (matrix D q false false) (matrix D q true true))
      (mul D (matrix D q false true) (matrix D q true false)))) (one D)

abbrev Table (n d : ℕ) := List ((Fin n → Bool) × Coefficient d)

/-- Explicit uniform truth-table order; no chosen Fintype equivalence is
invoked by the compiler. Empty arity has exactly one empty assignment. -/
def allWords : (n : ℕ) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n+1 => (allWords n).map (Fin.cons false) ++ (allWords n).map (Fin.cons true)

def denseTable (f : (Fin n → Bool) → Coefficient d) : Table n d :=
  (allWords n).map (fun x => (x,f x))

theorem allWords_length (n : ℕ) : (allWords n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allWords,ih,pow_succ,Nat.mul_comm,two_mul]

theorem mem_allWords (x : Fin n → Bool) : x ∈ allWords n := by
  induction n with
  | zero =>
    have h : x=Fin.elim0 := Subsingleton.elim _ _
    simp [allWords,h]
  | succ n ih =>
    have ht := ih (Fin.tail x)
    have he := Fin.cons_self_tail x
    cases h : x 0 with
    | false =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨Fin.tail x,ht,by simpa only [h] using he⟩
    | true =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨Fin.tail x,ht,by simpa only [h] using he⟩

theorem allWords_nodup (n : ℕ) : (allWords n).Nodup := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    have hi (b : Bool) : Function.Injective
        (fun x : Fin n → Bool => (Fin.cons b x : Fin (n+1) → Bool)) := by
      intro x y h
      exact congrArg Fin.tail h
    apply List.nodup_append.mpr
    refine ⟨ih.map (hi false),ih.map (hi true),?_⟩
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    have hz := congrFun hxy 0
    simp at hz

theorem sum_allWords {R : Type*} [AddCommMonoid R] (f : (Fin n → Bool) → R) :
    ((allWords n).map f).sum = ∑ x, f x := by
  have hu : (allWords n).toFinset = Finset.univ := by
    ext x
    simp [mem_allWords]
  rw [← List.sum_toFinset f (allWords_nodup n),hu]

/-- Emit the actual tensor product action, including the scalar table
coefficient of each row. There is no global-network assignment enumeration. -/
def vertex (D : ArithmeticData d) (A : Bool → Bool → Poly v d)
    (table : Table n d) (x : Fin n → Bool) : Poly v d :=
  total (table.map (fun row => mul D
    (product D (List.ofFn (fun j => A (x j) (row.1 j)))) (constant row.2)))

/-- Four literal terms implement Uᵀ E U, including both off-diagonal
entries separately. The same U used for the vertex inverse occurs here. -/
def edge (D : ArithmeticData d) (U : Bool → Bool → Poly v d)
    (E : Bool → Bool → Coefficient d) (a b : Bool) : Poly v d :=
  total ([false,true].flatMap (fun i => [false,true].map (fun j =>
    mul D (mul D (U i a) (constant (E i j))) (U j b))))

def affineEquation (D : ArithmeticData d) (A : Bool → Bool → Poly v d)
    (table : Table n d) (x : Fin n → Bool) (scale : Fin v)
    (phase : Coefficient d) : Poly v d :=
  sub (vertex D A table x) (mul D (variableCode D scale) (constant phase))

variable {K : Type*} [Field K] [Algebra ℚ K] (F : FixedField K d)
noncomputable section

@[simp] theorem denote_constant (c : Coefficient d) :
    denote F (constant (v:=v) c) = C (F.decode c) := by
  simp [constant]

@[simp] theorem denote_variable (j : Fin v) :
    denote F (variableCode F.toArithmeticData j) = X j := by
  have he : exponent (fun i : Fin v => if i=j then 1 else 0) = Finsupp.single j 1 := by
    ext i
    simp [Finsupp.single_apply,eq_comm]
  simp [variableCode,he,X]

@[simp] theorem denote_total (ps : List (Poly v d)) :
    denote F (total ps) = (ps.map (denote F)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change denote F (add p (total ps)) = _
    rw [denote_add,ih]
    rfl

@[simp] theorem denote_product (ps : List (Poly v d)) :
    denote F (product F.toArithmeticData ps) = (ps.map (denote F)).prod := by
  induction ps with
  | nil => exact denote_one F
  | cons p ps ih =>
    change denote F (mul F.toArithmeticData p (product F.toArithmeticData ps)) = _
    rw [denote_mul,ih]
    rfl

def point (x : Fin (5+q) → K) : SymbolicTransform.Variables (Fin q) → K :=
  Sum.elim (fun i => x (Fin.castAdd q i)) (fun i => x (Fin.natAdd 5 i))

theorem eval_matrix (x : Fin (5+q) → K) (a b : Bool) :
    aeval x (denote F (matrix F.toArithmeticData q a b)) =
      SymbolicTransform.matrix (point x) a b := by
  simp [matrix,SymbolicTransform.matrix,point]

theorem eval_inverse (x : Fin (5+q) → K) (a b : Bool) :
    aeval x (denote F (inverse F.toArithmeticData q a b)) =
      SymbolicTransform.inverse (point x) a b := by
  cases a <;> cases b <;>
    simp [inverse,matrix,SymbolicTransform.inverse,SymbolicTransform.adjugate,
      SymbolicTransform.matrix,SymbolicTransform.index,point]

theorem eval_guard (x : Fin (5+q) → K) :
    aeval x (denote F (guard F.toArithmeticData q)) =
      x (Fin.castAdd q 4) * SymbolicTransform.determinant
        (SymbolicTransform.matrix (point x)) - 1 := by
  simp [guard,matrix,SymbolicTransform.determinant,SymbolicTransform.matrix,point]

/-- Literal finite-table interpretation, including n=0 and repeated rows. -/
def signature (table : Table n d) : Signature K n :=
  fun y => (table.map (fun row => if y=row.1 then F.decode row.2 else 0)).sum

@[simp] theorem signature_denseTable (f : (Fin n → Bool) → Coefficient d) :
    signature F (denseTable f) = fun x => F.decode (f x) := by
  funext x
  simp [signature,denseTable,List.map_map,sum_allWords,Function.comp_def]

theorem vertex_eval (A : Bool → Bool → Poly v d) (table : Table n d)
    (z : Fin v → K) (x : Fin n → Bool) :
    aeval z (denote F (vertex F.toArithmeticData A table x)) =
      Signature.coordinateAction (fun _ a b => aeval z (denote F (A a b)))
        (signature F table) x := by
  induction table with
  | nil => simp [vertex,total,signature,Signature.coordinateAction]
  | cons row rows ih =>
    have hs : signature F (row::rows) =
        (fun y => if y=row.1 then F.decode row.2 else 0) + signature F rows := by
      funext y
      simp [signature]
    have ht : vertex F.toArithmeticData A (row::rows) x =
        add (mul F.toArithmeticData
          (product F.toArithmeticData (List.ofFn (fun j => A (x j) (row.1 j))))
          (constant row.2)) (vertex F.toArithmeticData A rows x) := rfl
    rw [ht,denote_add,map_add,ih,hs,Signature.coordinateAction_add]
    congr 1
    simp [denote_mul,denote_product,List.map_ofFn,List.prod_ofFn,
      Signature.coordinateAction,Finset.mul_sum,Finset.sum_mul]

theorem inverse_vertex_eval (table : Table n d) (z : Fin (5+q) → K)
    (x : Fin n → Bool) :
    aeval z (denote F (vertex F.toArithmeticData (inverse F.toArithmeticData q) table x)) =
      Signature.coordinateAction (fun _ => SymbolicTransform.inverse (point z))
        (signature F table) x := by
  rw [vertex_eval]
  simp only [eval_inverse]

theorem edge_eval (U : Bool → Bool → Poly v d)
    (E : Bool → Bool → Coefficient d) (z : Fin v → K) (a b : Bool) :
    aeval z (denote F (edge F.toArithmeticData U E a b)) =
      Kernel.pullback (fun i j => F.decode (E i j))
        (fun i j => aeval z (denote F (U i j))) a b := by
  simp [edge,Kernel.pullback,Kernel.mul,Kernel.transpose,
    denote_mul,denote_constant,mul_add,add_mul,mul_assoc] <;> ring

theorem affineEquation_eval (A : Bool → Bool → Poly v d) (table : Table n d)
    (x : Fin n → Bool) (scale : Fin v) (phase : Coefficient d) (z : Fin v → K) :
    aeval z (denote F (affineEquation F.toArithmeticData A table x scale phase)) =
      Signature.coordinateAction (fun _ a b => aeval z (denote F (A a b)))
        (signature F table) x - z scale * F.decode phase := by
  rw [affineEquation,denote_sub,map_sub,denote_mul,map_mul,vertex_eval]
  simp

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SparseTransform
