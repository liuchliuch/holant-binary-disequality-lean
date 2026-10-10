import Holant.Proofs.Algorithms.LocalAffine.NetworkGauge
import Holant.Proofs.Tractability.ProductMachine.Endpoint


namespace Holant.LocalDrafts.MainChain.LocalAffineSupport
open Holant.Tractable AffinePhase TwoTranslate
open LocalAffineTwists
noncomputable section

def impossible (n : ℕ) : AffineSystem n where
  rows := 1
  matrix _ _ := 0
  rhs _ := 1

theorem impossible_holds {n : ℕ} (x : Word n) : ¬ (impossible n).Holds x := by
  intro h
  have hh := h ⟨0, by simp [impossible]⟩
  simpa [impossible] using hh

/-- Zero local tensors use the explicit inconsistent equation 0=1. -/
theorem local_system_exists {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : LocalAffine f) : ∃ S : AffineSystem n, ∀ x, S.Holds x ↔ f x ≠ 0 := by
  by_cases hz : f = 0
  · refine ⟨impossible n, ?_⟩
    intro x
    simp [impossible_holds, hz]
  · obtain ⟨S,hS⟩ := support_system f hf hz
    exact ⟨S, fun x => (hS x).symm⟩

def localSystem {n : ℕ} (f : Signature AlgebraicComplex n) (hf : LocalAffine f) :
    AffineSystem n := (local_system_exists f hf).choose

theorem localSystem_holds {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : LocalAffine f) (x : Word n) : (localSystem f hf).Holds x ↔ f x ≠ 0 :=
  (local_system_exists f hf).choose_spec x

def stack {n : ℕ} : List (AffineSystem n) → AffineSystem n
  | [] => AffineSystem.unconstrained n
  | S :: ss => S.inter (stack ss)

theorem stack_holds {n : ℕ} (ss : List (AffineSystem n)) (x : Word n) :
    (stack ss).Holds x ↔ ∀ S ∈ ss, S.Holds x := by
  induction ss with
  | nil => simp [stack]
  | cons S ss ih => simp [stack, AffineSystem.inter_holds, ih]

theorem stack_rows {n : ℕ} (ss : List (AffineSystem n)) :
    (stack ss).rows = (ss.map AffineSystem.rows).sum := by
  induction ss <;> simp_all [stack, AffineSystem.inter, AffineSystem.unconstrained]

def assignment (E : ℕ) (x : Word (2*E)) : (Fin E × Bool) → Bool :=
  fun p => x (Holant.LocalDrafts.Tractability.ProductMachine.Endpoint.typed E p)

def assignmentEquiv (E : ℕ) : Word (2*E) ≃ ((Fin E × Bool) → Bool) where
  toFun := assignment E
  invFun z i := z ((Holant.LocalDrafts.Tractability.ProductMachine.Endpoint.equivalence E).symm i)
  left_inv x := by
    funext i
    exact congrArg x
      ((Holant.LocalDrafts.Tractability.ProductMachine.Endpoint.equivalence E).apply_symm_apply i)
  right_inv z := by
    funext p
    exact congrArg z
      ((Holant.LocalDrafts.Tractability.ProductMachine.Endpoint.equivalence E).symm_apply_apply p)

variable (G : Network AlgebraicComplex 0)

def vertexMap (v : Fin G.shape.vertices) (x : Word (2*G.shape.edges)) :
    Word (G.shape.arity v) := G.shape.assignment Fin.elim0 (assignment G.shape.edges x) v

def edgeMap (e : Fin G.shape.edges) (x : Word (2*G.shape.edges)) : Word 2 :=
  ![assignment G.shape.edges x (e,false), assignment G.shape.edges x (e,true)]

theorem vertexMap_affine (v : Fin G.shape.vertices) : IsAffineMap (vertexMap G v) := by
  intro x y
  funext j
  simp [vertexMap, NetworkShape.assignment_closed, assignment, AffinePhase.xor, origin]

theorem edgeMap_affine (e : Fin G.shape.edges) : IsAffineMap (edgeMap G e) := by
  intro x y
  funext j
  fin_cases j <;> simp [edgeMap, assignment, AffinePhase.xor, origin]

variable (hv : ∀ v, LocalAffine (G.vertex v))
variable (he : ∀ e, LocalAffine (kernelSignature (G.edge e)))

def vertexSystem (v : Fin G.shape.vertices) : AffineSystem (2*G.shape.edges) :=
  (localSystem (G.vertex v) (hv v)).pullback (vertexMap G v)

def edgeSystem (e : Fin G.shape.edges) : AffineSystem (2*G.shape.edges) :=
  (localSystem (kernelSignature (G.edge e)) (he e)).pullback (edgeMap G e)

def global : AffineSystem (2*G.shape.edges) :=
  stack (List.ofFn (vertexSystem G hv) ++ List.ofFn (edgeSystem G he))

theorem global_holds (x : Word (2*G.shape.edges)) :
    (global G hv he).Holds x ↔
      G.assignmentTerm Fin.elim0 (assignment G.shape.edges x) ≠ 0 := by
  simp only [global, stack_holds, List.forall_mem_append,
    List.forall_mem_ofFn_iff, vertexSystem, edgeSystem,
    AffineSystem.pullback_holds _ _ (vertexMap_affine G _),
    AffineSystem.pullback_holds _ _ (edgeMap_affine G _), localSystem_holds]
  simp [Network.assignmentTerm, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    vertexMap, edgeMap, kernelSignature]

theorem global_rows : (global G hv he).rows =
    (∑ v, (localSystem (G.vertex v) (hv v)).rows) +
      ∑ e, (localSystem (kernelSignature (G.edge e)) (he e)).rows := by
  simp [global, stack_rows, List.map_append, List.sum_append, List.map_ofFn,
    List.sum_ofFn, vertexSystem, edgeSystem, AffineSystem.pullback]

/-- Unsatisfiability of the actual support equations makes every summand zero.
The converse is deliberately absent: complex-valued cancellation is allowed. -/
theorem denote_zero_of_unsatisfiable
    (h : ¬ ∃ x, (global G hv he).Holds x) : G.denote Fin.elim0 = 0 := by
  change (∑ z, G.assignmentTerm Fin.elim0 z) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_contra hn
  apply h
  refine ⟨(assignmentEquiv G.shape.edges).symm z, ?_⟩
  apply (global_holds G hv he _).mpr
  change G.assignmentTerm Fin.elim0
    ((assignmentEquiv G.shape.edges) ((assignmentEquiv G.shape.edges).symm z)) ≠ 0
  simpa only [Equiv.apply_symm_apply] using hn

/-- A computed solution of these equations supplies precisely the reference
needed by the original-graph gauge identity, without new graph conditions. -/
theorem solution_affine_gauge (x : Word (2*G.shape.edges))
    (hx : (global G hv he).Holds x) :
    let reference := assignment G.shape.edges x
    (LocalAffineNetwork.gauged G reference).denote Fin.elim0 = G.denote Fin.elim0 ∧
      (∀ v, Affine ((LocalAffineNetwork.gauged G reference).vertex v)) ∧
      ∀ e, Affine (kernelSignature ((LocalAffineNetwork.gauged G reference).edge e)) := by
  have hn := (global_holds G hv he x).mp hx
  exact ⟨LocalAffineNetwork.denote_gauged G _,
    LocalAffineNetwork.gauged_vertices_affine G hv _ hn,
    LocalAffineNetwork.gauged_edges_affine G he _ hn⟩

end
end Holant.LocalDrafts.MainChain.LocalAffineSupport
