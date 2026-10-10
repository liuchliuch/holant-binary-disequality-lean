import Holant.Proofs.Tractability.ProductSource
import Holant.Network
import Holant.Tractable.CommonTransform


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.ProductElimination

open Holant.Tractable
open scoped BigOperators

variable {K : Type*} [CommSemiring K]

def Factor.rename {m n : ℕ} (r : Fin m → Fin n) (f : Factor K m) : Factor K n :=
  f.substitute (fun i => (r i, false))

theorem weight_rename {m n : ℕ} (r : Fin m → Fin n)
    (fs : List (Factor K m)) (x : Fin n → Bool) :
    weight (fs.map (Factor.rename r)) x = weight fs (fun i => x (r i)) := by
  change weight (fs.map (Factor.substitute (fun i => (r i, false)))) x = _
  simpa only [Bool.xor_false] using weight_substitute (fun i => (r i, false)) fs x

theorem weight_append {n : ℕ} (fs gs : List (Factor K n)) (x : Fin n → Bool) :
    weight (fs ++ gs) x = weight fs x * weight gs x := by
  simp [weight, List.prod_append]

theorem weight_flatten {n : ℕ} (fss : List (List (Factor K n))) (x : Fin n → Bool) :
    weight fss.flatten x = (fss.map (fun fs => weight fs x)).prod := by
  induction fss with
  | nil => rfl
  | cons fs fss ih => simp [List.flatten_cons, weight_append, ih]

theorem weight_blocks {n m : ℕ} (fs : Fin m → List (Factor K n)) (x : Fin n → Bool) :
    weight (List.ofFn fs).flatten x = ∏ i, weight (fs i) x := by
  rw [weight_flatten]
  simp [List.map_ofFn, List.prod_ofFn]

noncomputable section

variable (N : Holant.Network AlgebraicComplex 0)

abbrev variableCount := Fintype.card (Fin N.shape.edges × Bool)

def endNumbering : (Fin N.shape.edges × Bool) ≃ Fin (variableCount N) := Fintype.equivFin _

/-- Closed networks have no external ports. This is the actual ordered port map. -/
def portEnd (v : Fin N.shape.vertices) (i : Fin (N.shape.arity v)) : Fin N.shape.edges × Bool :=
  Sum.elim Fin.elim0 id (N.shape.ports ⟨v, i⟩)

def assignment (x : Fin (variableCount N) → Bool) : (Fin N.shape.edges × Bool) → Bool :=
  fun e => x ((endNumbering N) e)

theorem assignment_at_port (x : Fin (variableCount N) → Bool)
    (v : Fin N.shape.vertices) (i : Fin (N.shape.arity v)) :
    N.shape.assignment Fin.elim0 ((assignment N) x) v i =
      x ((endNumbering N) ((portEnd N) v i)) := by
  cases hp : N.shape.ports ⟨v, i⟩ with
  | inl a => exact Fin.elim0 a
  | inr e => simp [Holant.NetworkShape.assignment, assignment, portEnd, hp]

/-- Product witnesses are local formulas for actual vertex and edge labels. -/
structure NetworkPresentation where
  vertex : ∀ v, Presentation (N.vertex v)
  edge : ∀ e, Presentation (kernelSignature (N.edge e))

variable (P : NetworkPresentation N)

def vertexFactors (v : Fin N.shape.vertices) : List (Factor AlgebraicComplex (variableCount N)) :=
  (P.vertex v).factors.map (Factor.rename (fun i => (endNumbering N) ((portEnd N) v i)))

def edgeFactors (e : Fin N.shape.edges) : List (Factor AlgebraicComplex (variableCount N)) :=
  (P.edge e).factors.map (Factor.rename (fun i : Fin 2 => (endNumbering N) (e, i == 1)))

def networkFactors : List (Factor AlgebraicComplex (variableCount N)) :=
  (List.ofFn (vertexFactors N P)).flatten ++ (List.ofFn (edgeFactors N P)).flatten

theorem vertexFactors_weight (v : Fin N.shape.vertices) (x : Fin (variableCount N) → Bool) :
    weight (vertexFactors N P v) x = N.vertex v (N.shape.assignment Fin.elim0 ((assignment N) x) v) := by
  rw [vertexFactors, weight_rename, (P.vertex v).localFormula]
  congr 1
  funext i
  exact ((assignment_at_port N) x v i).symm

theorem edgeFactors_weight (e : Fin N.shape.edges) (x : Fin (variableCount N) → Bool) :
    weight (edgeFactors N P e) x =
      N.edge e ((assignment N) x (e, false)) ((assignment N) x (e, true)) := by
  rw [edgeFactors, weight_rename, (P.edge e).localFormula]
  rfl

theorem networkFactors_weight (x : Fin (variableCount N) → Bool) :
    weight (networkFactors N P) x =
      (∏ v, N.vertex v (N.shape.assignment Fin.elim0 ((assignment N) x) v)) *
        ∏ e, N.edge e ((assignment N) x (e, false)) ((assignment N) x (e, true)) := by
  simp only [networkFactors, weight_append, weight_blocks,
    vertexFactors_weight, edgeFactors_weight]

def assignmentEquiv : (Fin (variableCount N) → Bool) ≃ ((Fin N.shape.edges × Bool) → Bool) where
  toFun := (assignment N)
  invFun x := fun i => x ((endNumbering N).symm i)
  left_inv x := by funext i; simp [assignment]
  right_inv x := by funext e; simp [assignment]

/-- A derived equality with the actual network sum, not a supplied value oracle. -/
theorem partition_network : partition (networkFactors N P) = N.denote Fin.elim0 := by
  unfold partition Holant.Network.denote
  simp_rw [networkFactors_weight]
  exact (assignmentEquiv N).sum_comp (fun y =>
    (∏ v, N.vertex v (N.shape.assignment Fin.elim0 y v)) * ∏ e, N.edge e (y (e,false)) (y (e,true)))

theorem evaluate_network : evaluate (networkFactors N P) = N.denote Fin.elim0 := by
  rw [evaluate_eq_partition, partition_network]

theorem networkFactors_length :
    (networkFactors N P).length =
      (∑ v, (P.vertex v).factors.length) + ∑ e, (P.edge e).factors.length := by
  simp [networkFactors, vertexFactors, edgeFactors, List.length_flatten,
    List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem run_network :
    (run (networkFactors N P)).1 = N.denote Fin.elim0 ∧
    (run (networkFactors N P)).2 ≤
      (2 * (variableCount N) + 1) *
        ((∑ v, (P.vertex v).factors.length) + ∑ e, (P.edge e).factors.length) +
        2 * (variableCount N) := by
  constructor
  · rw [run_exact, partition_network]
  · simpa only [networkFactors_length] using run_operations_le (networkFactors N P)

/-- Extract local formula data from the genuine source Product predicate.
Choice is offline data selection, not a claimed effective recognition procedure. -/
def presentationOfProduct (hv : ∀ v, Product (N.vertex v))
    (he : ∀ e, Product (kernelSignature (N.edge e))) : NetworkPresentation N where
  vertex v := ofProduct (hv v)
  edge e := ofProduct (he e)

theorem evaluate_of_product (hv : ∀ v, Product (N.vertex v))
    (he : ∀ e, Product (kernelSignature (N.edge e))) :
    evaluate (networkFactors N (presentationOfProduct N hv he)) = N.denote Fin.elim0 :=
  evaluate_network N _

end
end Holant.LocalDrafts.Tractability.ProductElimination
