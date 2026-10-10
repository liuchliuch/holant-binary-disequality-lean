import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZPrime
import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZFactors
import Holant.Proofs.Closure.ClosureMarkedCyclic

/-! The semantic GHZ triangle action is the genuine common coordinate
change. Invertibility transports tensor primality without asserting any
physical availability of the decomposing matrices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZAction
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
namespace T
export GlobalCloseCompletionTernaryGHZCore (action core ghz triangle triangle_value)
export GlobalCloseCompletionTernaryGHZPrime (core_prime)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

def words : Bool×Bool×Bool ≃ (Fin 3→Bool) where
  toFun x:=![x.1,x.2.1,x.2.2]
  invFun x:=(x 0,x 1,x 2)
  left_inv:=by intro x;rcases x with ⟨a,b,c⟩;rfl
  right_inv:=by intro x;funext i;fin_cases i <;> rfl

theorem sum_words {K : Type} [AddCommMonoid K] (f : (Fin 3→Bool)→K) :
    (∑x,f x)=∑i : Bool,∑j : Bool,∑k : Bool,f ![i,j,k] := by
  rw [←words.sum_comp f]
  simp only [Fintype.sum_prod_type,words,Equiv.coe_fn_mk]

theorem coordinate {K : Type} [Field K] (A : Matrix Bool Bool K) (f : Signature K 3) :
    Signature.coordinateAction (fun _=>A) f=T.action A f := by
  funext x
  simp only [Signature.coordinateAction,sum_words,T.action]
  simp [Fin.prod_univ_three,mul_assoc]

theorem det (A : InvertibleKernel) : (Matrix.of A.matrix).det≠0 :=
  (Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedCyclic.coordinateGL A).det_ne_zero

theorem triangle_prime (A B C : InvertibleKernel)
    (nonzero : ((Matrix.of B.matrix).transpose*(Matrix.of C.matrix)) false false≠0 ∨
      ((Matrix.of B.matrix).transpose*(Matrix.of C.matrix)) true true≠0) :
    Prime (⟨3,T.triangle (T.ghz A.matrix B.matrix C.matrix)⟩ : AnySignature AlgebraicComplex) := by
  let M : Matrix Bool Bool AlgebraicComplex:=(Matrix.of B.matrix).transpose*(Matrix.of C.matrix)
  have hm : M.det≠0 := by
    dsimp only [M]
    rw [Matrix.det_mul,Matrix.det_transpose]
    exact mul_ne_zero (det B) (det C)
  have hdet : M false false*M true true-M false true*M true false≠0 := by
    have formula : M.det=M false false*M true true-M false true*M true false := by
      rw [←Matrix.det_reindex_self finTwoEquiv.symm M,Matrix.det_fin_two]
      rfl
    rwa [formula] at hm
  have hp:=T.core_prime (M false false) (M false true) (M true false) (M true true) hdet nonzero
  have acted:=(GlobalCloseCompletionTernaryGHZFactors.prime_action_iff A
    (⟨3,T.core (M false false) (M false true) (M true false) (M true true)⟩ : AnySignature AlgebraicComplex)).mpr hp
  change Prime (⟨3,Signature.coordinateAction (fun _=>A.matrix) _⟩ : AnySignature AlgebraicComplex) at acted
  rw [coordinate] at acted
  have he : T.ghz A.matrix B.matrix C.matrix=T.ghz (Matrix.of A.matrix) (Matrix.of B.matrix) (Matrix.of C.matrix) := by
    funext x
    simp only [T.ghz,Matrix.of_apply]
  rw [he,T.triangle_value]
  have heA : (Matrix.of A.matrix : Matrix Bool Bool AlgebraicComplex)=A.matrix := by
    funext i j
    rfl
  rw [heA]
  exact acted

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZAction
end
