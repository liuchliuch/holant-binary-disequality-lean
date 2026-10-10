import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginFlipGraph
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginNormalizationPhase

/-! Every normalization coefficient comes from one actual antidiagonal
vertex. Finite induction retains all original labels and ordinary edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginNormalizationGraph
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {arity : ℕ→ℕ}
variable {H : (j : Fin s)→Signature K (arity j.val)}

def shiftSet (S : Finset (Fin (n+2))) (x : Fin (n+2)→Bool) : Fin (n+2)→Bool :=
  fun i=>if i∈S then !(x i) else x i

theorem shift_insert (S : Finset (Fin (n+2))) (i : Fin (n+2)) (hi : i∉S)
    (x : Fin (n+2)→Bool) :
    shiftSet S (NoXOriginFlipGraph.flipAt i x)=shiftSet (insert i S) x := by
  classical
  funext j
  by_cases hj : j=i
  · subst j;simp [shiftSet,NoXOriginFlipGraph.flipAt,hi]
  · simp [shiftSet,NoXOriginFlipGraph.flipAt,hj]

theorem exists_graph (N : M.Macro H (n+2)) (A : M.Macro H 2) (v w : K)
    (anti : A.network.denote=NoXWeightedAntiSigned.anti v w) (S : Finset (Fin (n+2))) :
    ∃Q : M.Macro H (n+2),∀x,Q.network.denote x=
      (∏i∈S,if x i then v else w)*N.network.denote (shiftSet S x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨N,fun x=>?_⟩
    have empty : shiftSet (∅ : Finset (Fin (n+2))) x=x := by
      funext i;simp [shiftSet]
    rw [Finset.prod_empty,one_mul,empty]
  | @insert i S hi ih =>
    obtain ⟨Q,hQ⟩ := ih
    refine ⟨NoXOriginFlipGraph.graph Q A i,?_⟩
    intro x
    rw [NoXOriginFlipGraph.graph_value Q A i v w anti,hQ,shift_insert S i hi,Finset.prod_insert hi]
    have prod : (∏j∈S,if NoXOriginFlipGraph.flipAt i x j then v else w)=
        ∏j∈S,if x j then v else w := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j≠i := by intro h;subst j;exact hi hj
      simp only [NoXOriginFlipGraph.flipAt,Function.update_of_ne hji]
    rw [prod,mul_assoc]

variable {H' : (j : Fin s)→Signature AlgebraicComplex (arity j.val)}

theorem exists_normalized (N : M.Macro H' (n+2)) (A : M.Macro H' 2)
    (v w : AlgebraicComplex) (anti : A.network.denote=NoXWeightedAntiSigned.anti v w)
    (a : Word (n+2)) :
    ∃Q : M.Macro H' (n+2),Q.network.denote=NoXOriginNormalizationPhase.normalized N.network.denote a v w := by
  classical
  let S := Finset.univ.filter (fun i=>a i=true)
  obtain ⟨Q,hQ⟩ := exists_graph N A v w anti S
  refine ⟨Q,funext fun x=>?_⟩
  rw [hQ,NoXOriginNormalizationPhase.normalized,NoXOriginNormalizationPhase.weight]
  have shift : shiftSet S x=xor a x := by
    funext i
    cases ha : a i <;> simp [shiftSet,S,AffinePhase.xor,ha]
  rw [shift]
  congr 1
  simp only [S,Finset.prod_filter]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginNormalizationGraph
end
