import Holant.Network
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Literal network polynomials for the designated binary occurrences in
source Lemma3.1. The same theorem permits arbitrary arities and open boundaries.
It preserves the original incidence structure, including loops and parallel
edges. No interpolation algorithm or bit-cost conclusion is asserted here. -/
namespace Holant.Complexity.BinaryInterpolation
open scoped BigOperators
noncomputable section
variable {K : Type*} [CommSemiring K] {n : ℕ}

def linearEntry (a b : K) : Polynomial K := Polynomial.C a+Polynomial.C b*Polynomial.X

theorem linearEntry_degree (a b : K) : (linearEntry a b).natDegree≤1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_C_mul_le b Polynomial.X).trans Polynomial.natDegree_X_le

@[simp] theorem linearEntry_coeff_one (a b : K) : (linearEntry a b).coeff 1=b := by
  simp [linearEntry]

/-- Marked vertices receive the exact pencil L+zR; all other labels and every
edge tensor remain the caller's original data. -/
def pencilNetwork (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v)) (z : K) : Network K n where
  shape := N.shape
  vertex v x := if v∈S then L v x+z*R v x else N.vertex v x
  edge := N.edge

def rightNetwork (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v)) : Network K n where
  shape := N.shape
  vertex v x := if v∈S then R v x else N.vertex v x
  edge := N.edge

def fixedWeight (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (x : Fin n → Bool) (z : (Fin N.shape.edges×Bool)→Bool) : K :=
  (∏v∈Sᶜ,N.vertex v (N.shape.assignment x z v))*
    ∏e,N.edge e (z (e,false)) (z (e,true))

def networkPolynomial (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (x : Fin n → Bool) : Polynomial K :=
  ∑z : (Fin N.shape.edges×Bool)→Bool,
    Polynomial.C (fixedWeight N S x z)*
      ∏v∈S,linearEntry (L v (N.shape.assignment x z v)) (R v (N.shape.assignment x z v))

theorem prod_cases {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (f g : V→K) :
    (∏v,if v∈S then f v else g v)=(∏v∈S,f v)*(∏v∈Sᶜ,g v) := by
  rw [Finset.prod_ite]
  have h₁ : Finset.univ.filter (fun v => v∈S)=S := by ext v; simp
  have h₂ : Finset.univ.filter (fun v => v∉S)=Sᶜ := by ext v; simp
  rw [h₁,h₂]

theorem networkPolynomial_eval (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (x : Fin n → Bool) (t : K) :
    (networkPolynomial N S L R x).eval t=(pencilNetwork N S L R t).denote x := by
  simp only [networkPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_prod,linearEntry,Polynomial.eval_add,Polynomial.eval_X]
  unfold Network.denote pencilNetwork
  apply Finset.sum_congr rfl
  intro z _
  rw [prod_cases]
  simp only [fixedWeight]
  simp_rw [mul_comm t]
  ring

theorem networkPolynomial_degree (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (x : Fin n → Bool) : (networkPolynomial N S L R x).natDegree≤S.card := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑v∈S,1 := Finset.sum_le_sum (fun v _ => linearEntry_degree _ _)
    _ = S.card := by simp

theorem networkPolynomial_top_coefficient (N : Network K n) (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
    (x : Fin n → Bool) :
    (networkPolynomial N S L R x).coeff S.card=(rightNetwork N S R).denote x := by
  simp only [networkPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul]
  unfold Network.denote rightNetwork
  apply Finset.sum_congr rfl
  intro z _
  rw [prod_cases]
  have hc := Polynomial.coeff_prod_of_natDegree_le S
    (fun v => linearEntry (L v (N.shape.assignment x z v)) (R v (N.shape.assignment x z v)))
    1 (fun _ _ => linearEntry_degree _ _)
  simp only [mul_one,linearEntry_coeff_one] at hc
  rw [hc]
  simp only [fixedWeight]
  ring

end
end Holant.Complexity.BinaryInterpolation
