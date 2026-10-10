import Holant.Proofs.Tractability.ProductFamily
import Holant.Proofs.Tractability.ProductMachine.FiniteLabels


namespace Holant.LocalDrafts.Tractability.ProductMachine.FamilyCatalogue

open Holant.Tractable Holant.Complexity Holant.Algebraic
open ProductElimination
open scoped BigOperators
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ}

def leaf {n : ℕ} : Factor AlgebraicComplex n → Bool → AlgebraicComplex
  | .scalar c, _ => c
  | .unary _ u, bit => u bit
  | .link _ _ _, _ => 1

def addressFactor {A : Type} {n : ℕ} (f : Factor AlgebraicComplex n)
    (address : Bool → A) : LabelledFactor A n :=
  match f with
  | .scalar _ => .scalar (address false)
  | .unary j _ => .unary j address
  | .link i j p => .link i j p

/-- This small substitution lemma is instantiated below by exact indexed
lookup identities. It is not an extra assumption of the family solver. -/
theorem addressFactor_realize {A : Type} {n : ℕ} (f : Factor AlgebraicComplex n)
    (address : Bool → A) (values : A → AlgebraicComplex)
    (h : ∀ bit, values (address bit) = leaf f bit) :
    (addressFactor f address).realize values = f := by
  cases f with
  | scalar c => exact congrArg Factor.scalar (h false)
  | unary j u => exact congrArg (Factor.unary j) (funext h)
  | link i j p => rfl

variable (D : FamilyData s b arity)

abbrev VertexSlot := Σ i : Fin s, Fin (D.vertex i).factors.length × Bool
abbrev EdgeSlot := Σ i : Fin b, Fin (D.edge i).factors.length × Bool
abbrev Slot := VertexSlot D ⊕ EdgeSlot D

def extra : Slot D → AlgebraicComplex
  | .inl ⟨i, k, bit⟩ => leaf ((D.vertex i).factors.get k) bit
  | .inr ⟨i, k, bit⟩ => leaf ((D.edge i).factors.get k) bit

def labelCount : ℕ := Fintype.card (Slot D)
def labels : Slot D ≃ Fin (labelCount D) := Fintype.equivFin (Slot D)
def coefficient (a : Fin (labelCount D)) : AlgebraicComplex := extra D ((labels D).symm a)

def vertexAddress (i : Fin s) (k : Fin (D.vertex i).factors.length) (bit : Bool) : Fin (labelCount D) :=
  labels D (.inl ⟨i, k, bit⟩)
def edgeAddress (i : Fin b) (k : Fin (D.edge i).factors.length) (bit : Bool) : Fin (labelCount D) :=
  labels D (.inr ⟨i, k, bit⟩)

@[simp] theorem vertex_lookup (i : Fin s) (k : Fin (D.vertex i).factors.length) (bit : Bool) :
    coefficient D (vertexAddress D i k bit) = leaf ((D.vertex i).factors.get k) bit := by
  simp [coefficient, vertexAddress, extra]

@[simp] theorem edge_lookup (i : Fin b) (k : Fin (D.edge i).factors.length) (bit : Bool) :
    coefficient D (edgeAddress D i k bit) = leaf ((D.edge i).factors.get k) bit := by
  simp [coefficient, edgeAddress, extra]

/-- The finite alphabet is bounded by the concrete factor lists, even when
there are no factors or some signatures are nullary. Repetition is intentional. -/
theorem labelCount_eq : labelCount D = 2 * D.templateBudget := by
  simp [labelCount, Slot, VertexSlot, EdgeSlot, Fintype.card_sigma, Fintype.card_prod,
    FamilyData.templateBudget, Finset.sum_mul, ← Finset.mul_sum, Nat.mul_add, Nat.mul_comm]

def vertices (i : Fin s) : List (LabelledFactor (Fin (labelCount D)) (arity i.val)) :=
  List.ofFn (fun k : Fin (D.vertex i).factors.length =>
    addressFactor ((D.vertex i).factors.get k) (vertexAddress D i k))

def edges (i : Fin b) : List (LabelledFactor (Fin (labelCount D)) 2) :=
  List.ofFn (fun k : Fin (D.edge i).factors.length =>
    addressFactor ((D.edge i).factors.get k) (edgeAddress D i k))

theorem vertices_realize (i : Fin s) :
    (vertices D i).map (LabelledFactor.realize (coefficient D)) = (D.vertex i).factors := by
  simp only [vertices, List.map_ofFn, Function.comp_def]
  have h : (fun k : Fin (D.vertex i).factors.length =>
      (addressFactor ((D.vertex i).factors.get k) (vertexAddress D i k)).realize (coefficient D)) =
      (D.vertex i).factors.get := by
    funext k
    exact addressFactor_realize _ _ _ (vertex_lookup D i k)
  rw [h, List.ofFn_get]

theorem edges_realize (i : Fin b) :
    (edges D i).map (LabelledFactor.realize (coefficient D)) = (D.edge i).factors := by
  simp only [edges, List.map_ofFn, Function.comp_def]
  have h : (fun k : Fin (D.edge i).factors.length =>
      (addressFactor ((D.edge i).factors.get k) (edgeAddress D i k)).realize (coefficient D)) =
      (D.edge i).factors.get := by
    funext k
    exact addressFactor_realize _ _ _ (edge_lookup D i k)
  rw [h, List.ofFn_get]

theorem vertex_formula (i : Fin s) (x : Fin (arity i.val) → Bool) :
    ProductElimination.weight ((vertices D i).map (LabelledFactor.realize (coefficient D))) x = D.signatures i x := by
  rw [vertices_realize]
  exact (D.vertex i).localFormula x

theorem edge_formula (i : Fin b) (x : Fin 2 → Bool) :
    ProductElimination.weight ((edges D i).map (LabelledFactor.realize (coefficient D))) x = D.kernels i (x 0) (x 1) := by
  rw [edges_realize]
  exact (D.edge i).localFormula x

@[simp] theorem vertices_length (i : Fin s) : (vertices D i).length = (D.vertex i).factors.length := by
  simp [vertices]
@[simp] theorem edges_length (i : Fin b) : (edges D i).length = (D.edge i).factors.length := by
  simp [edges]

/-- Explicit coverage of every scalar/unary slot, derived from list membership.
This concerns decomposition coefficients, not just original signature entries. -/
theorem vertex_leaf_covered (i : Fin s) (f : Factor AlgebraicComplex (arity i.val))
    (hf : f ∈ (D.vertex i).factors) (bit : Bool) :
    ∃ a : Fin (labelCount D), coefficient D a = leaf f bit := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hf
  exact ⟨vertexAddress D i k bit, (vertex_lookup D i k bit).trans (congrArg (fun f => leaf f bit) hk)⟩

theorem edge_leaf_covered (i : Fin b) (f : Factor AlgebraicComplex 2)
    (hf : f ∈ (D.edge i).factors) (bit : Bool) :
    ∃ a : Fin (labelCount D), coefficient D a = leaf f bit := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hf
  exact ⟨edgeAddress D i k bit, (edge_lookup D i k bit).trans (congrArg (fun f => leaf f bit) hk)⟩

/-- Fin ports are retained by constructor, rather than introduced through an
unproved runtime port-coverage condition. -/
def ports {A : Type} {n : ℕ} : LabelledFactor A n → List (Fin n)
  | .scalar _ => []
  | .unary j _ => [j]
  | .link i j _ => [i, j]

def sourcePorts {n : ℕ} : Factor AlgebraicComplex n → List (Fin n)
  | .scalar _ => []
  | .unary j _ => [j]
  | .link i j _ => [i, j]

theorem addressFactor_ports {A : Type} {n : ℕ} (f : Factor AlgebraicComplex n) (a : Bool → A) :
    ports (addressFactor f a) = sourcePorts f := by cases f <;> rfl

theorem vertices_ports (i : Fin s) :
    (vertices D i).map ports = (D.vertex i).factors.map sourcePorts := by
  simp only [vertices, List.map_ofFn, Function.comp_def, addressFactor_ports]
  simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map sourcePorts) (List.ofFn_get (D.vertex i).factors)

theorem edges_ports (i : Fin b) :
    (edges D i).map ports = (D.edge i).factors.map sourcePorts := by
  simp only [edges, List.map_ofFn, Function.comp_def, addressFactor_ports]
  simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map sourcePorts) (List.ofFn_get (D.edge i).factors)

end
end Holant.LocalDrafts.Tractability.ProductMachine.FamilyCatalogue
