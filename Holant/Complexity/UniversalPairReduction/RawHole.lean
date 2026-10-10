import Holant.Complexity.ClosedNetworkSemantics
import Mathlib.Tactic.FinCases
import Holant.Complexity.UniversalPairReduction.BinaryTable

/-! The removed-vertex raw tensor as an actual finite sum over the original
validated instance. Every original edge factor is retained, including self-loops,
and every other vertex factor is retained, including nullary components. -/
noncomputable section
namespace Holant.Complexity.UniversalPairReduction
open scoped BigOperators

variable {K : Type*} [CommSemiring K]

/-- A literal factor deletion, without any graph-normalization assumption. -/
def holeWeight (N : Network K 0) (v : Fin N.shape.vertices)
    (z : (Fin N.shape.edges × Bool) → Bool) : K :=
  (∏ u ∈ Finset.univ.erase v, N.vertex u (N.shape.assignment Fin.elim0 z u)) *
    ∏ e, N.edge e (z (e,false)) (z (e,true))

def rawHole (N : Network K 0) (v : Fin N.shape.vertices) :
    Signature K (N.shape.arity v) := fun x =>
  ∑ z : (Fin N.shape.edges × Bool) → Bool,
    if N.shape.assignment Fin.elim0 z v = x then holeWeight N v z else 0

/-- This is the raw, uncorrected tensor: the marked vertex is contracted
against its original ordered port bits, not against complemented coordinates. -/
theorem denote_eq_contract_rawHole (N : Network K 0) (v : Fin N.shape.vertices) :
    N.denote Fin.elim0 = ∑ x, N.vertex v x * rawHole N v x := by
  classical
  unfold rawHole
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro z _
  simp only [mul_ite,mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ,if_true,holeWeight]
  rw [←mul_assoc]
  congr 1
  exact (Finset.mul_prod_erase Finset.univ
    (fun u => N.vertex u (N.shape.assignment Fin.elim0 z u)) (Finset.mem_univ v)).symm

/-- Exact agreement of every non-marked vertex suffices for equality of raw
holes. No arity, parity, charge or nonzero condition is imposed on those factors. -/
theorem rawHole_congr (s : NetworkShape 0)
    (f g : (u : Fin s.vertices) → Signature K (s.arity u))
    (E : Fin s.edges → Bool → Bool → K) (v : Fin s.vertices)
    (h : ∀u, u ≠ v → f u = g u) :
    rawHole ⟨s,f,E⟩ v = rawHole ⟨s,g,E⟩ v := by
  classical
  funext x
  unfold rawHole
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  unfold holeWeight
  congr 1
  apply Finset.prod_congr rfl
  intro u hu
  dsimp only
  rw [h u (Finset.mem_erase.mp hu).1]

/-- Binary coordinates use the original zero/one port order. -/
def binaryRaw (N : Network K 0) (v : Fin N.shape.vertices)
    (h : N.shape.arity v = 2) : BinaryTable K :=
  fun a b => rawHole N v (fun i => (![a,b] : Fin 2 → Bool) (Fin.cast h i))

/-- Enumerate the four possible ordered binary words, with the arity transport
proved once rather than treating the input as a precomputed matrix. -/
theorem sum_binary {m : ℕ} (h : m=2) (f : (Fin m → Bool) → K) :
    (∑ x, f x) =
      f (fun i => (![false,false] : Fin 2 → Bool) (Fin.cast h i)) +
      f (fun i => (![false,true] : Fin 2 → Bool) (Fin.cast h i)) +
      f (fun i => (![true,false] : Fin 2 → Bool) (Fin.cast h i)) +
      f (fun i => (![true,true] : Fin 2 → Bool) (Fin.cast h i)) := by
  subst m
  rw [←(piFinTwoEquiv (fun _ : Fin 2 => Bool)).symm.sum_comp]
  have hw (a b : Bool) : Fin.cons a (Fin.cons b finZeroElim) =
      (![a,b] : Fin 2 → Bool) := by
    funext i
    fin_cases i <;> rfl
  simp [Fintype.sum_prod_type,piFinTwoEquiv,hw,add_assoc,add_comm,add_left_comm]

/-- The literal partition value is the ordered four-entry insertion pairing. -/
theorem denote_eq_binary_insert (N : Network K 0) (v : Fin N.shape.vertices)
    (h : N.shape.arity v=2) :
    N.denote Fin.elim0 = (binaryRaw N v h).insert
      (fun a b => N.vertex v (fun i => (![a,b] : Fin 2 → Bool) (Fin.cast h i))) := by
  rw [denote_eq_contract_rawHole N v,sum_binary h]
  rfl

/-- In particular the input value is h01 when the marked original vertex is
Delta. All other factors still come from the original input's full network. -/
theorem denote_delta (N : Network K 0) (v : Fin N.shape.vertices)
    (h : N.shape.arity v=2)
    (hv : ∀ a b, N.vertex v (fun i => (![a,b] : Fin 2 → Bool) (Fin.cast h i)) =
      BinaryTable.delta a b) :
    N.denote Fin.elim0 = binaryRaw N v h false true := by
  rw [denote_eq_binary_insert N v h]
  have he : (fun a b => N.vertex v (fun i => (![a,b] : Fin 2 → Bool) (Fin.cast h i))) =
      BinaryTable.delta := funext fun a => funext (hv a)
  rw [he,BinaryTable.insert_delta]

end Holant.Complexity.UniversalPairReduction
