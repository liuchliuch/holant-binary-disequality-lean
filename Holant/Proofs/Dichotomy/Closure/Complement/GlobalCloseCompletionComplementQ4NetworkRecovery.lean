import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ColoredRecovery
import Holant.Complexity.BinaryInterpolation.NetworkPolynomial

/-! Exact network semantics for four-mode extraction, including arbitrary
old vertices and edge kernels. The exponential coloring sum is used only
in the proof; recovery samples only polynomially many physical powers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NetworkRecovery
open Holant Holant.Complexity.BinaryInterpolation
open scoped BigOperators
namespace R
export GlobalCloseCompletionComplementQ4ColoredRecovery (recover)
end R
namespace A
export GlobalCloseCompletionComplementQ4Annihilator (annihilator moment)
end A
namespace B
export GlobalCloseCompletionComplementQ4Nodes (node Separated)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}
variable (N : Network K n) (S : Finset (Fin N.shape.vertices))
variable (basis : Fin 4→(v : Fin N.shape.vertices)→Signature K (N.shape.arity v))

def network (u : Fin 4→K) : Network K n where
  shape:=N.shape
  vertex v x:=if v∈S then ∑i,u i*basis i v x else N.vertex v x
  edge:=N.edge

def coefficient (x : Fin n→Bool) (color : S→Fin 4) : K:=
  ∑z : (Fin N.shape.edges×Bool)→Bool,
    fixedWeight N S x z * ∏v : S,basis (color v) v.val (N.shape.assignment x z v.val)

theorem assignment_expansion (u : Fin 4→K) (x : Fin n→Bool) (z : (Fin N.shape.edges×Bool)→Bool) :
    (∏v∈S,∑i,u i*basis i v (N.shape.assignment x z v))*fixedWeight N S x z=
      ∑color : S→Fin 4,(∏v : S,u (color v))*
        (fixedWeight N S x z*∏v : S,basis (color v) v.val (N.shape.assignment x z v.val)) := by
  classical
  rw [←Finset.prod_coe_sort,Fintype.prod_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro color _
  rw [Finset.prod_mul_distrib]
  ring

theorem expansion (u : Fin 4→K) (x : Fin n→Bool) :
    (network N S basis u).denote x=
      ∑color : S→Fin 4,coefficient N S basis x color*(∏v : S,u (color v)) := by
  classical
  unfold Network.denote network
  simp only []
  simp_rw [prod_cases]
  have summand (z : (Fin N.shape.edges×Bool)→Bool) :
      ((∏v∈S,∑i,u i*basis i v (N.shape.assignment x z v))*
        ∏v∈Sᶜ,N.vertex v (N.shape.assignment x z v))*
          ∏e,N.edge e (z (e,false)) (z (e,true))=
      ∑color : S→Fin 4,(∏v : S,u (color v))*
        (fixedWeight N S x z*∏v : S,basis (color v) v.val (N.shape.assignment x z v.val)) := by
    rw [mul_assoc]
    exact assignment_expansion N S basis u x z
  simp_rw [summand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro color _
  rw [←Finset.mul_sum]
  exact mul_comm _ _

theorem powers (v : Fin 4→K) (k : ℕ) (x : Fin n→Bool) :
    (network N S basis (fun i=>v i^k)).denote x=
      ∑color : S→Fin 4,coefficient N S basis x color*(∏p : S,v (color p))^k := by
  rw [expansion]
  simp_rw [Finset.prod_pow]

theorem pure (j : Fin 4) (x : Fin n→Bool) :
    coefficient N S basis x (fun _=>j)=(rightNetwork N S (basis j)).denote x := by
  classical
  unfold coefficient Network.denote rightNetwork
  apply Finset.sum_congr rfl
  intro z _
  rw [prod_cases]
  dsimp only
  rw [Finset.prod_coe_sort S (fun v=>basis j v (N.shape.assignment x z v))]
  unfold fixedWeight
  ring

theorem recover (v : Fin 4→K) (j : Fin 4) (separated : B.Separated v j) (x : Fin n→Bool) :
    A.moment (A.annihilator (B.node v j (Fintype.card S)))
      (fun k=>(network N S basis (fun i=>v i^k)).denote x) /
      (v j^(Fintype.card S)*∏m,(v j^(Fintype.card S)-B.node v j (Fintype.card S) m))=
      (rightNetwork N S (basis j)).denote x := by
  classical
  have result:=R.recover (V:=S) v j separated (coefficient N S basis x)
  simpa only [powers,pure] using result

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NetworkRecovery
end
