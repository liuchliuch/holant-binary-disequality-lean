import Holant.OneHot.Computable.Components
import Holant.Proofs.Hardness.GeneralCSPUnused

/-! Literal parity double-cover components.  The graph retains every input link,
including parallel links and loops. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityComponents
open Holant.OneHot.Computable Holant.OneHot.Decomposition
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Links (n : ℕ) := List ((Fin n × Fin n) × Bool)
def vertex {n : ℕ} (i : Fin n) (b : Bool) : Fin (n*2) :=
  finProdFinEquiv (i, if b then 1 else 0)
def graph {n : ℕ} (links : Links n) : Graph :=
  ⟨n*2, links.flatMap fun q =>
    [(vertex q.1.1 false,vertex q.1.2 q.2),
     (vertex q.1.1 true,vertex q.1.2 (!q.2))]⟩
def Consistent {n : ℕ} (links : Links n) (x : Fin n → Bool) : Prop :=
  ∀ q ∈ links, x q.1.1 = Bool.xor (x q.1.2) q.2
local instance {n : ℕ} (links : Links n) (x : Fin n → Bool) : Decidable (Consistent links x) := Classical.propDecidable _
def label {n : ℕ} (links : Links n) (i : Fin n) (b : Bool) : Fin (n*2) :=
  (graph links).label (vertex i b)
def scope {n : ℕ} (links : Links n) (i : Fin n) : Fin (n*2) :=
  min (label links i false) (label links i true)
def signs {n : ℕ} (links : Links n) (i : Fin n) : Bool :=
  decide (label links i true < label links i false)
def Good {n : ℕ} (links : Links n) : Prop :=
  ∀ i, label links i false ≠ label links i true

def lifted {n : ℕ} (x : Fin n → Bool) (v : Fin (n*2)) : Bool :=
  Bool.xor (x (finProdFinEquiv.symm v).1) (decide ((finProdFinEquiv.symm v).2 = 1))
@[simp] theorem lifted_vertex {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    lifted x (vertex i b) = Bool.xor (x i) b := by
  cases b <;> simp [lifted,vertex]

theorem lifted_edge {n : ℕ} (links : Links n) (x : Fin n → Bool)
    (hx : Consistent links x) (e : (graph links).Edge) :
    lifted x ((graph links).endpoint e false) =
      lifted x ((graph links).endpoint e true) := by
  have he : (graph links).edges.get e ∈ (graph links).edges := List.get_mem _ _
  change _ ∈ links.flatMap _ at he
  rcases List.mem_flatMap.mp he with ⟨q,hq,he⟩
  have h := hx q hq
  change lifted x ((graph links).edges.get e).1 = lifted x ((graph links).edges.get e).2
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he | he
  · rw [he]
    simp only [lifted_vertex,Bool.xor_false]
    exact h
  · rw [he]
    simp only [lifted_vertex]
    rw [h]
    cases x q.1.2 <;> cases q.2 <;> rfl

theorem lifted_reachable {n : ℕ} (links : Links n) (x : Fin n → Bool)
    (hx : Consistent links x) {u v : (graph links).Vertex}
    (h : Relation.EqvGen (Link (graph links).endpoint) u v) :
    lifted x u = lifted x v := by
  induction h with
  | rel a b h =>
    rcases h with ⟨e,rfl,rfl⟩
    exact lifted_edge links x hx e
  | refl => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem good_of_consistent {n : ℕ} (links : Links n) (x : Fin n → Bool)
    (hx : Consistent links x) : Good links := by
  intro i hi
  have hr := (graph links).label_eq_iff (vertex i false) (vertex i true)
  have h := lifted_reachable links x hx (hr.mp hi)
  simp only [lifted_vertex] at h
  cases x i <;> simp at h

theorem inconsistent_sum_zero {n : ℕ} (links : Links n) (h : ¬ Good links)
    {K : Type*} [CommSemiring K] (w : (Fin n → Bool) → K) :
    (∑ x, if Consistent links x then w x else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  simp only [show ¬ Consistent links x from fun hx => h (good_of_consistent links x hx), ite_false]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityComponents
