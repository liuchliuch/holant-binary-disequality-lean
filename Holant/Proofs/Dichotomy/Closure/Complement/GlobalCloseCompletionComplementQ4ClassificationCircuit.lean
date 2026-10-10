import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Templates

/-! Four unchanged quaternary rows on K4, joined by six literal native-X
edges. The boundary order is chosen to expose its redundant middle block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationCircuit
open Holant
open scoped BigOperators
namespace T
export GlobalCloseCompletionComplementQ4Templates (tensor reindex contract)
end T
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor_denote reindex_denote)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384
set_option Elab.async false

def order : Equiv.Perm (Fin 16) where
  toFun := ![12,0,4,2,14,6,1,8,13,10,7,3,15,5,11,9]
  invFun := ![1,6,3,11,2,13,5,10,7,15,9,14,0,8,4,12]
  left_inv := by decide
  right_inv := by decide

variable {K : Type} [Field K]

def circuit (q : Signature K 4) : Signature K 4 :=
  Signature.contract Signature.disequality (Signature.contract Signature.disequality
    (Signature.contract Signature.disequality (Signature.contract Signature.disequality
      (Signature.contract Signature.disequality (Signature.contract Signature.disequality
        (Tensor.reindex order (Signature.tensor (Signature.tensor q q) (Signature.tensor q q))))))))

theorem input (q : Signature K 4) (x : Fin 4→Bool) (a b c d e f g h i j k l : Bool) :
    Tensor.reindex order (Signature.tensor (Signature.tensor q q) (Signature.tensor q q))
      (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e (Fin.cons f
        (Fin.cons g (Fin.cons h (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l x))))))))))))=
      (q ![x 0,a,e,c]*q ![x 2,g,b,i])*(q ![x 1,k,h,d]*q ![x 3,f,l,j]) := by
  simp only [Tensor.reindex,Signature.tensor_apply]
  congr 2 <;> apply congrArg q <;> funext z <;> fin_cases z <;> rfl

def term (q : Signature K 4) (x : Fin 4→Bool) (i j k l m n : Bool) : K :=
  (q ![x 0,i,k,j]*q ![x 2,l,!i,m])*(q ![x 1,n,!l,!j]*q ![x 3,!k,!n,!m])
def value (q : Signature K 4) (x : Fin 4→Bool) : K :=
  ∑n : Bool,∑m : Bool,∑l : Bool,∑k : Bool,∑j : Bool,∑i : Bool,term q x i j k l m n

theorem circuit_value (q : Signature K 4) (x : Fin 4→Bool) : circuit q x=value q x := by
  simp only [circuit,Signature.contract_disequality]
  simp only [input q x false true false true false true false true false true false true,
    input q x false true false true false true false true false true true false,
    input q x false true false true false true false true true false false true,
    input q x false true false true false true false true true false true false,
    input q x false true false true false true true false false true false true,
    input q x false true false true false true true false false true true false,
    input q x false true false true false true true false true false false true,
    input q x false true false true false true true false true false true false,
    input q x false true false true true false false true false true false true,
    input q x false true false true true false false true false true true false,
    input q x false true false true true false false true true false false true,
    input q x false true false true true false false true true false true false,
    input q x false true false true true false true false false true false true,
    input q x false true false true true false true false false true true false,
    input q x false true false true true false true false true false false true,
    input q x false true false true true false true false true false true false,
    input q x false true true false false true false true false true false true,
    input q x false true true false false true false true false true true false,
    input q x false true true false false true false true true false false true,
    input q x false true true false false true false true true false true false,
    input q x false true true false false true true false false true false true,
    input q x false true true false false true true false false true true false,
    input q x false true true false false true true false true false false true,
    input q x false true true false false true true false true false true false,
    input q x false true true false true false false true false true false true,
    input q x false true true false true false false true false true true false,
    input q x false true true false true false false true true false false true,
    input q x false true true false true false false true true false true false,
    input q x false true true false true false true false false true false true,
    input q x false true true false true false true false false true true false,
    input q x false true true false true false true false true false false true,
    input q x false true true false true false true false true false true false,
    input q x true false false true false true false true false true false true,
    input q x true false false true false true false true false true true false,
    input q x true false false true false true false true true false false true,
    input q x true false false true false true false true true false true false,
    input q x true false false true false true true false false true false true,
    input q x true false false true false true true false false true true false,
    input q x true false false true false true true false true false false true,
    input q x true false false true false true true false true false true false,
    input q x true false false true true false false true false true false true,
    input q x true false false true true false false true false true true false,
    input q x true false false true true false false true true false false true,
    input q x true false false true true false false true true false true false,
    input q x true false false true true false true false false true false true,
    input q x true false false true true false true false false true true false,
    input q x true false false true true false true false true false false true,
    input q x true false false true true false true false true false true false,
    input q x true false true false false true false true false true false true,
    input q x true false true false false true false true false true true false,
    input q x true false true false false true false true true false false true,
    input q x true false true false false true false true true false true false,
    input q x true false true false false true true false false true false true,
    input q x true false true false false true true false false true true false,
    input q x true false true false false true true false true false false true,
    input q x true false true false false true true false true false true false,
    input q x true false true false true false false true false true false true,
    input q x true false true false true false false true false true true false,
    input q x true false true false true false false true true false false true,
    input q x true false true false true false false true true false true false,
    input q x true false true false true false true false false true false true,
    input q x true false true false true false true false false true true false,
    input q x true false true false true false true false true false false true,
    input q x true false true false true false true false true false true false]
  simp only [value,Fintype.sum_bool,term,Bool.not_true,Bool.not_false]
  ac_rfl

variable [Algebra ℚ K] {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val))
variable (N : NativeAntiTargetSource.Output H 4)

def output : NativeAntiTargetSource.Output H 4 :=
  T.contract H (n:=4) (T.contract H (n:=6) (T.contract H (n:=8)
    (T.contract H (n:=10) (T.contract H (n:=12) (T.contract H (n:=14)
      (T.reindex H (n:=16) (T.tensor H (m:=8) (n:=8) (T.tensor H (m:=4) (n:=4) N N) (T.tensor H (m:=4) (n:=4) N N)) order))))))

theorem denote : (output H N).network.denote=circuit N.network.denote := by
  simp only [output,T.contract,T.reindex,T.tensor,Network.denote_contract,C.reindex_denote,C.tensor_denote,circuit]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationCircuit
end
