import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseActual
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetPair

/-! The explicit three-vertex native-X network for the selected dense
cancellation row. Its labels are the original q row and the two genuinely
interpolated antidiagonals; no identity vertex occurs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex tensor_denote reindex_denote binarySignature)
end C
namespace O
export PaperTerminalBridgeDenseOrders (order reordered)
end O
namespace D
export PaperTerminalBridgeDenseCancellation (dress)
end D
namespace A
export NativeAntiTargetAlgebra (anti)
end A
namespace S
export NativeAntiTargetSource (Output)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def connection : Equiv.Perm (Fin 8) where
  toFun := ![0,2,6,7,4,1,5,3]
  invFun := ![0,5,1,7,4,6,2,3]
  left_inv := by decide
  right_inv := by decide

def network (f : Signature K 4) (k : Fin 3) (r t : K) : Network K 4 :=
  ((C.reindex (C.tensor
    (C.tensor (C.reindex (Network.corolla f) (O.order k)) (Network.corolla (C.binarySignature (A.anti 1 r))))
    (Network.corolla (C.binarySignature (A.anti 1 t)))) connection).contract Signature.disequality).contract Signature.disequality

theorem input (f : Signature K 4) (r t : K) (a b c d : Bool) (x : Fin 4→Bool) :
    Tensor.reindex connection (Signature.tensor (Signature.tensor f (C.binarySignature (A.anti 1 r)))
      (C.binarySignature (A.anti 1 t))) (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))))=
      f ![a,c,x 2,x 3]*A.anti 1 r (x 0) b*A.anti 1 t (x 1) d := by
  simp only [Tensor.reindex_apply,Signature.tensor_apply,C.binarySignature]
  congr 2
  apply congrArg f
  funext i
  fin_cases i <;> rfl

theorem value (f : Signature K 4) (k : Fin 3) (r t : K) :
    (network f k r t).denote=D.dress (O.reordered f k) r t := by
  funext x
  rw [network,Network.denote_contract,Network.denote_contract,C.reindex_denote,
    C.tensor_denote,C.tensor_denote,C.reindex_denote,Network.denote_corolla,
    Network.denote_corolla,Network.denote_corolla]
  simp only [Signature.contract_disequality]
  rw [input _ r t false true false true x,input _ r t true false false true x,
    input _ r t false true true false x,input _ r t true false true false x]
  have word : ![x 0,x 1,x 2,x 3]=x := by funext i;fin_cases i <;>rfl
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp only [A.anti,h0,h1,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,
      mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,D.dress]
  all_goals simp only [h0,h1] at word
  all_goals rw [word]
  all_goals simp only [O.reordered]
  all_goals first | rfl | ring

variable {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))
variable (f : Signature K 4) (k : Fin 3) (r t : K) (qLabel rLabel tLabel : Fin s)
variable (qLiteral : (⟨a qLabel.val,H qLabel⟩ : AnySignature K)=⟨4,f⟩)
variable (rLiteral : (⟨a rLabel.val,H rLabel⟩ : AnySignature K)=⟨2,C.binarySignature (A.anti 1 r)⟩)
variable (tLiteral : (⟨a tLabel.val,H tLabel⟩ : AnySignature K)=⟨2,C.binarySignature (A.anti 1 t)⟩)

def labels : Labelling (network f k r t).shape s 1 a where
  vertex v := ![qLabel,rLabel,tLabel] v
  vertex_arity v := by
    change Fin 3 at v
    fin_cases v
    · exact congrArg Sigma.fst qLiteral
    · exact congrArg Sigma.fst rLiteral
    · exact congrArg Sigma.fst tLiteral
  edge _ := 0

def output : S.Output H 4 where
  network := network f k r t
  labels := labels H f k r t qLabel rLabel tLabel qLiteral rLiteral tLiteral
  exact := by
    intro v
    change Fin 3 at v
    fin_cases v
    · exact qLiteral
    · exact rLiteral
    · exact tLiteral
  native := by
    intro e
    change Fin 2 at e
    fin_cases e <;> rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseNetwork
end
