import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgePinFactor

/-! The literal q4 plus two zero pins yields a nonsingular weighted equality
on the remaining two ports. Native X edges force the two q inputs to one;
the resulting diagonal entries are the original y and x coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgePinNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex tensor_denote reindex_denote binarySignature)
end C
namespace P
export PaperTerminalBridgePinFactor (pin)
end P
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
namespace S
export NativeAntiTargetSource (Output)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]

def connection : Equiv.Perm (Fin 6) where
  toFun := ![0,2,4,5,1,3]
  invFun := ![0,4,1,5,2,3]
  left_inv := by decide
  right_inv := by decide

def network (f : Signature K 4) : Network K 2 :=
  ((C.reindex (C.tensor (C.tensor (Network.corolla f) (Network.corolla (P.pin false)))
    (Network.corolla (P.pin false))) connection).contract Signature.disequality).contract Signature.disequality

theorem input (f : Signature K 4) (a b c d : Bool) (x : Fin 2→Bool) :
    Tensor.reindex connection (Signature.tensor (Signature.tensor f (P.pin false)) (P.pin false))
      (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))))=
      f ![a,c,x 0,x 1]*(if b then 0 else 1)*(if d then 0 else 1) := by
  simp only [Tensor.reindex_apply,Signature.tensor_apply,P.pin]
  have word : (fun i : Fin 4=>
      (show Fin 6→Bool from Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))))
        (connection (Fin.castAdd 1 (Fin.castAdd 1 i))))=![a,c,x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [word]
  cases b <;> cases d <;> rfl

theorem value (f : Signature K 4) (even : EvenSupport f) :
    (network f).denote=C.binarySignature (D.diagonal (entries f).y (entries f).x) := by
  funext x
  rw [network,Network.denote_contract,Network.denote_contract,C.reindex_denote,
    C.tensor_denote,C.tensor_denote,Network.denote_corolla,Network.denote_corolla]
  simp only [Signature.contract_disequality]
  rw [input _ false true false true x,input _ true false false true x,
    input _ false true true false x,input _ true false true false x]
  simp only [mul_zero,mul_one,zero_add,add_zero]
  rw [←table_entries f even]
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [table,entries,C.binarySignature,D.diagonal,h0,h1]

variable {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (f : Signature K 4) (qLabel pLabel : Fin s)
variable (qLiteral : (⟨a qLabel.val,H qLabel⟩ : AnySignature K)=⟨4,f⟩)
variable (pLiteral : (⟨a pLabel.val,H pLabel⟩ : AnySignature K)=⟨1,P.pin false⟩)

def output : S.Output H 2 where
  network := network f
  labels := {
    vertex v := ![qLabel,pLabel,pLabel] v
    vertex_arity v := by
      change Fin 3 at v
      fin_cases v
      · exact congrArg Sigma.fst qLiteral
      · exact congrArg Sigma.fst pLiteral
      · exact congrArg Sigma.fst pLiteral
    edge _ := 0 }
  exact := by
    intro v
    change Fin 3 at v
    fin_cases v
    · exact qLiteral
    · exact pLiteral
    · exact pLiteral
  native := by
    intro e
    change Fin 2 at e
    fin_cases e <;> rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgePinNetwork
end
