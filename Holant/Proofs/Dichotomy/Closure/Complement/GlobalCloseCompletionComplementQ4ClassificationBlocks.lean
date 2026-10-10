import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationReduction
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationIsing

/-! Actual native-X operations on a two-block row: its series square,
EO square, pure Eq4 case, and explicit nonsingular diagonal factorization. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationBlocks
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export GlobalCloseCompletionComplementQ4Series (row connected)
end S
namespace T
export GlobalCloseCompletionComplementQ4Templates (connect connect_network reindex)
end T
namespace R
export GlobalCloseCompletionComplementQ4ClassificationReduction (swap_bc)
end R
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (symmetric)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {size : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val))

def swap (N : NativeAntiTargetSource.Output H 4) : NativeAntiTargetSource.Output H 4 :=
  T.reindex H N (Equiv.swap 1 2)
theorem swap_value (N : NativeAntiTargetSource.Output H 4) :
    (swap H N).network.denote=Tensor.reindex (Equiv.swap 1 2) N.network.denote :=
  Holant.Complexity.BinaryInterpolation.Chains.reindex_denote _ _

def square (N : NativeAntiTargetSource.Output H 4) : NativeAntiTargetSource.Output H 4:=T.connect H N N

theorem square_value (N : NativeAntiTargetSource.Output H 4) (a b : K)
    (form : N.network.denote=S.row a b 0 0) :
    (square H N).network.denote=S.row (2*a*b) (a^2+b^2) 0 0 := by
  rw [square,T.connect_network,S.connected _ _ _ _ _ _ _ _ _ _ form form]
  congr 1 <;> ring

def eo (N : NativeAntiTargetSource.Output H 4) : NativeAntiTargetSource.Output H 4:=
  swap H (square H (swap H N))

theorem eo_value (N : NativeAntiTargetSource.Output H 4) (a b : K)
    (form : N.network.denote=S.row a b 0 0) :
    (eo H N).network.denote=EOBinaryPlaneCore.lift (M.binary (P.symmetric (a^2) (b^2))) := by
  have hf : (swap H N).network.denote=S.row a 0 b 0 := by rw [swap_value,form,R.swap_bc]
  rw [eo,swap_value,square,T.connect_network,S.connected _ _ _ _ _ _ _ _ _ _ hf hf]
  have alg : S.row (a*0+0*a) (a*a+0*0) (b*0+0*b) (b*b+0*0)=S.row 0 (a^2) 0 (b^2) := by
    congr 1 <;> ring
  rw [alg,R.swap_bc]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,EOBinaryPlaneCore.lift,
      M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3]

def Pure : Prop:=∃N : NativeAntiTargetSource.Output H 4,∃c : K,c≠0 ∧
  N.network.denote=c • Holant.EightVertex.ProductAnchor.equalityFour

theorem pure_row (a : K) : S.row a 0 0 0=a • Holant.EightVertex.ProductAnchor.equalityFour := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3]

theorem pure_of_zero (N : NativeAntiTargetSource.Output H 4) (a : K) (ha : a≠0)
    (form : N.network.denote=S.row a 0 0 0) : Pure H :=
  ⟨N,a,ha,form.trans (pure_row a)⟩

def diagonal (p q : K) : Signature K 2:=fun x=>if x 0=x 1 then (if x 0 then q else p) else 0

structure DiagonalProduct where
  graph : NativeAntiTargetSource.Output H 4
  scale : K
  ratio : K
  scale_ne : scale≠0
  ratio_ne : ratio≠0
  value : graph.network.denote=fun x=>scale*Signature.tensor (diagonal 1 ratio) (diagonal 1 ratio) x

theorem product_of_equal_square (N : NativeAntiTargetSource.Output H 4) (a b : K)
    (ha : a≠0) (hb : b≠0) (form : N.network.denote=S.row a b 0 0) (squares : a^2=b^2) :
    Nonempty (DiagonalProduct H) := by
  refine ⟨⟨N,a,b/a,ha,div_ne_zero hb ha,?_⟩⟩
  rw [form]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,Signature.tensor_apply,
      diagonal,h0,h1,h2,h3]
  all_goals field_simp [ha] <;> linear_combination squares

theorem pure_of_fourth (N : NativeAntiTargetSource.Output H 4) (a b : K)
    (ha : a≠0) (hb : b≠0) (form : N.network.denote=S.row a b 0 0)
    (different : a^2≠b^2) (fourth : a^4=b^4) : Pure H := by
  have pair : (a^2-b^2)*(a^2+b^2)=0 := by linear_combination fourth
  have sum : a^2+b^2=0 := (mul_eq_zero.mp pair).resolve_left (sub_ne_zero.mpr different)
  refine pure_of_zero H (square H N) (2*a*b) (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb) ?_
  rw [square_value H N a b form,sum]

theorem repaired (N Q : NativeAntiTargetSource.Output H 4) (b p q r s : K)
    (block : N.network.denote=S.row 0 b 0 0) (seed : Q.network.denote=S.row p q r s) :
    (T.connect H N Q).network.denote=S.row (b*p) (b*q) 0 0 := by
  rw [T.connect_network,S.connected _ _ _ _ _ _ _ _ _ _ block seed]
  congr 1 <;> ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationBlocks
end
