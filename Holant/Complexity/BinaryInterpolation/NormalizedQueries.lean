import Holant.Complexity.BinaryInterpolation.LagrangeValues
import Holant.NetworkAlgebra

/-! Exact normalization of query values at the original marked occurrences.
The scalar is charged once per occurrence, including repeated labels, loops,
and disconnected components. This is a semantic interpolation theorem; the
query graph compiler and field-arithmetic machine are separate obligations. -/
namespace Holant.Complexity.BinaryInterpolation
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def queryNetwork (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (Q : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v)) : Network K n where
  shape := N.shape
  vertex v x := if v∈S then Q v x else N.vertex v x
  edge := N.edge

theorem queryNetwork_value (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L R Q : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (c z : K) (hQ : ∀v∈S,∀x,Q v x=c*(L v x+z*R v x)) (x : Fin n→Bool) :
    (queryNetwork N S Q).denote x=c^S.card*(pencilNetwork N S L R z).denote x := by
  have he : (queryNetwork N S Q).denote x=
      ((pencilNetwork N S L R z).scaleVertices (fun v => if v∈S then c else 1)).denote x := by
    apply congrFun (Network.denote_congr N.shape _ _ _ _ ?_ ?_) x
    · intro v y
      change (if v∈S then Q v y else N.vertex v y)=
        (if v∈S then c else 1)*(if v∈S then L v y+z*R v y else N.vertex v y)
      by_cases hv : v∈S
      · simp only [if_pos hv,hQ v hv y]
      · simp only [if_neg hv,one_mul]
    · intros; rfl
  rw [he,Network.denote_scaleVertices,prod_cases]
  simp

/-- The actual query values determine the target with the exact scalar power,
including m=0. No zero query is discarded or divided by its value. -/
theorem normalized_query_recovery (N : Network K n)
    (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (nodes c : Fin (S.card+1)→K)
    (Q : Fin (S.card+1)→(v : Fin N.shape.vertices)→Signature K (N.shape.arity v))
    (hi : Function.Injective nodes) (hc : ∀i,c i≠0)
    (hQ : ∀i,∀v∈S,∀x,Q i v x=c i*(L v x+nodes i*R v x))
    (x : Fin n→Bool) :
    recoverTop nodes (fun i => (queryNetwork N S (Q i)).denote x/(c i)^S.card)=
      (rightNetwork N S R).denote x := by
  have he : (fun i => (queryNetwork N S (Q i)).denote x/(c i)^S.card)=
      (fun i => (pencilNetwork N S L R (nodes i)).denote x) := by
    funext i
    rw [queryNetwork_value N S L R (Q i) (c i) (nodes i) (hQ i) x]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (hc i))
  rw [he]
  exact network_interpolation N S L R x nodes hi

theorem positive_natural_nodes_injective [CharZero K] (m : ℕ) :
    Function.Injective (fun i : Fin (m+1) => ((i.val+1:ℕ):K)) := by
  intro i j h
  exact Fin.ext (Nat.add_right_cancel (Nat.cast_injective h))

end
end Holant.Complexity.BinaryInterpolation
