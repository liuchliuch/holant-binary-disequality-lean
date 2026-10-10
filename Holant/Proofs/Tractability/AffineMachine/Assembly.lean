import Holant.Proofs.Tractability.AffineMachine.ScalarCode
import Holant.Proofs.Tractability.ProductMachine.Endpoint
import Holant.Complexity.ClosedNetworkSemantics
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Records


namespace Holant.LocalDrafts.Tractability.AffineMachine.Assembly

open Holant.Tractable AffinePhase TwoTranslate
open Holant.Complexity
open FixedGadgetSubstitution.Compiler
open ProductMachine
open scoped BigOperators
noncomputable section

def phaseAdd {n : ℕ} (P Q : QuadraticPhase n) : QuadraticPhase n where
  constant := P.constant + Q.constant
  linear j := P.linear j + Q.linear j
  mixed j k := P.mixed j k + Q.mixed j k
  even_mixed j k h := by
    rcases P.even_mixed j k h with hp | hp <;>
      rcases Q.even_mixed j k h with hq | hq <;> simp only [hp, hq] <;> decide

theorem phaseAdd_eval {n : ℕ} (P Q : QuadraticPhase n) (x : Word n) :
    (phaseAdd P Q).eval x = P.eval x + Q.eval x := by
  have h (j k : Fin n) :
      (if j < k then (P.mixed j k + Q.mixed j k) * bitValue (ZMod 4) (x j) * bitValue (ZMod 4) (x k) else 0) =
      (if j < k then P.mixed j k * bitValue (ZMod 4) (x j) * bitValue (ZMod 4) (x k) else 0) +
      (if j < k then Q.mixed j k * bitValue (ZMod 4) (x j) * bitValue (ZMod 4) (x k) else 0) := by
    split <;> simp_all [add_mul]
  simp only [QuadraticPhase.eval, phaseAdd]
  simp_rw [h]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

def unit (n : ℕ) : State n := ⟨1, AffineSystem.unconstrained n, QuadraticPhase.zero n⟩

def merge {n : ℕ} (A B : State n) : State n :=
  ⟨A.scale * B.scale, A.support.inter B.support, phaseAdd A.phase B.phase⟩

theorem merge_value {n : ℕ} (A B : State n) (x : Word n) :
    (merge A B).value x = A.value x * B.value x := by
  by_cases ha : A.support.Holds x <;> by_cases hb : B.support.Holds x <;>
    simp [State.value, affineFormula, merge, AffineSystem.inter_holds, ha, hb,
      phaseAdd_eval, fourthRootPhase_add, mul_assoc, mul_comm, mul_left_comm]

def collect {n : ℕ} : List (State n) → State n
  | [] => unit n
  | A :: as => merge A (collect as)

theorem collect_value {n : ℕ} (as : List (State n)) (x : Word n) :
    (collect as).value x = (as.map (fun A => A.value x)).prod := by
  induction as with
  | nil => simp [collect, unit, State.value, affineFormula]
  | cons A as ih => simp [collect, merge_value, ih]

theorem collect_scale {n : ℕ} (as : List (State n)) :
    (collect as).scale = (as.map State.scale).prod := by
  induction as <;> simp_all [collect, merge, unit]

theorem collect_rows {n : ℕ} (as : List (State n)) :
    (collect as).support.rows = (as.map (fun A => A.support.rows)).sum := by
  induction as <;> simp_all [collect, merge, unit, AffineSystem.inter, AffineSystem.unconstrained]

def place {m n : ℕ} (route : Fin m → Fin n) (A : State m) : State n where
  scale := A.scale
  support := A.support.pullback (fun x j => x (route j))
  phase := Reconstruction.pullback A.phase (fun x j => x (route j)) (coordinates_isAffineMap route)

theorem place_value {m n : ℕ} (route : Fin m → Fin n) (A : State m) (x : Word n) :
    (place route A).value x = A.value (fun j => x (route j)) := by
  simp [place, State.value, affineFormula, AffineSystem.pullback_holds,
    coordinates_isAffineMap, Reconstruction.pullback_eval]

theorem presentation_exists {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f) :
    ∃ A : State n, A.value = f := by
  rcases hf with rfl | ⟨scale, _, S, Q, rfl⟩
  · refine ⟨⟨0, AffineSystem.unconstrained n, QuadraticPhase.zero n⟩, ?_⟩
    funext x
    simp [State.value, affineFormula]
  · exact ⟨⟨scale, S, Q⟩, rfl⟩

def ofAffine {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f) : State n :=
  (presentation_exists hf).choose

theorem ofAffine_value {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f) :
    (ofAffine hf).value = f := (presentation_exists hf).choose_spec

structure Family (s b : ℕ) (arity : ℕ → ℕ) where
  signatures : (i : Fin s) → Signature AlgebraicComplex (arity i.val)
  kernels : Fin b → Bool → Bool → AlgebraicComplex
  vertexAffine : ∀ i, Affine (signatures i)
  edgeAffine : ∀ i, Affine (fun x : Word 2 => kernels i (x 0) (x 1))

variable {s b : ℕ} {arity : ℕ → ℕ} (D : Family s b arity)

def vertex (i : Fin s) := ofAffine (D.vertexAffine i)
def edge (i : Fin b) := ofAffine (D.edgeAffine i)

def vertexBlock (r : Input s b arity) (v : Fin r.val.vertices.length) : State (2 * r.val.edges.length) :=
  place (fun j => ProductMachine.Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v, j⟩))
    (vertex D (r.val.signatureLabel r.property v))

def edgeBlock (r : Input s b arity) (e : Fin r.val.edges.length) : State (2 * r.val.edges.length) :=
  place (fun j : Fin 2 => ProductMachine.Endpoint.typed r.val.edges.length (e, j == 1))
    (edge D (r.val.edgeLabel r.property e))

def blocks (r : Input s b arity) : List (State (2 * r.val.edges.length)) :=
  List.ofFn (vertexBlock D r) ++ List.ofFn (edgeBlock D r)

def global (r : Input s b arity) : State (2 * r.val.edges.length) := collect (blocks D r)

set_option backward.isDefEq.respectTransparency false in
theorem vertexBlock_value (r : Input s b arity) (v : Fin r.val.vertices.length)
    (x : Word (2 * r.val.edges.length)) :
    (vertexBlock D r v).value x = D.signatures (r.val.signatureLabel r.property v)
      (fun j => x (ProductMachine.Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v, j⟩))) := by
  have h := place_value
    (fun j => ProductMachine.Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v,j⟩))
    (vertex D (r.val.signatureLabel r.property v)) x
  exact h.trans (congrFun (ofAffine_value (D.vertexAffine (r.val.signatureLabel r.property v))) _)

theorem edgeBlock_value (r : Input s b arity) (e : Fin r.val.edges.length)
    (x : Word (2 * r.val.edges.length)) :
    (edgeBlock D r e).value x = D.kernels (r.val.edgeLabel r.property e)
      (x (ProductMachine.Endpoint.typed r.val.edges.length (e, false)))
      (x (ProductMachine.Endpoint.typed r.val.edges.length (e, true))) := by
  rw [edgeBlock, place_value, edge, ofAffine_value]
  rfl

def assignmentEquiv (E : ℕ) : Word (2 * E) ≃ ((Fin E × Bool) → Bool) where
  toFun x e := x (ProductMachine.Endpoint.typed E e)
  invFun x i := x ((ProductMachine.Endpoint.equivalence E).symm i)
  left_inv x := by funext i; exact congrArg x ((ProductMachine.Endpoint.equivalence E).apply_symm_apply i)
  right_inv x := by funext e; exact congrArg x ((ProductMachine.Endpoint.equivalence E).symm_apply_apply e)

set_option backward.isDefEq.respectTransparency false in
theorem global_partition (r : Input s b arity) :
    (global D r).partition = (r.val.realize r.property D.signatures D.kernels).denote Fin.elim0 := by
  unfold State.partition global
  simp_rw [collect_value]
  simp only [blocks, List.map_append, List.prod_append, List.map_ofFn, List.prod_ofFn,
    Function.comp_def, vertexBlock_value, edgeBlock_value]
  unfold Holant.Network.denote
  exact
    (assignmentEquiv r.val.edges.length).sum_comp (fun z =>
      (∏ v, D.signatures (r.val.signatureLabel r.property v) (fun j => z (r.val.route r.property ⟨v, j⟩))) *
        ∏ e, D.kernels (r.val.edgeLabel r.property e) (z (e, false)) (z (e, true)))

def answer (r : Input s b arity) : AlgebraicComplex := evaluate (global D r)

theorem answer_exact (r : Input s b arity) :
    answer D r = (r.val.realize r.property D.signatures D.kernels).denote Fin.elim0 := by
  rw [answer, evaluate_eq_partition, global_partition]

/-- One static constant bounds rows of every local witness, including zeros. -/
def rowBudget : ℕ := (∑ i, (vertex D i).support.rows) + ∑ i, (edge D i).support.rows

theorem global_rows_le (r : Input s b arity) :
    (global D r).support.rows ≤ (r.val.vertices.length + r.val.edges.length) * rowBudget D := by
  have hv (i : Fin s) : (vertex D i).support.rows ≤ rowBudget D := by
    exact (Finset.single_le_sum (f := fun j => (vertex D j).support.rows)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_right _ _)
  have he (i : Fin b) : (edge D i).support.rows ≤ rowBudget D := by
    exact (Finset.single_le_sum (f := fun j => (edge D j).support.rows)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_left _ _)
  rw [global, collect_rows]
  simp only [blocks, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
    vertexBlock, edgeBlock, place, AffineSystem.pullback]
  calc
    _ ≤ (∑ _ : Fin r.val.vertices.length, rowBudget D) +
        ∑ _ : Fin r.val.edges.length, rowBudget D :=
      Nat.add_le_add (Finset.sum_le_sum (fun v _ => hv _)) (Finset.sum_le_sum (fun e _ => he _))
    _ = _ := by simp [Nat.add_mul]

end
end Holant.LocalDrafts.Tractability.AffineMachine.Assembly
