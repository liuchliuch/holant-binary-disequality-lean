import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Templates
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIWeightedEqualitySource

/-! A real two-X-edge cap of pure quaternary equality. The cap preserves the
original dictionary and all scalars, and detects a nonzero diagonal cofactor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureEqualityCap
open Holant Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
namespace O
export NativeAntiTargetSource (Output)
end O
namespace G
export GlobalCloseCompletionComplementQ4Templates (tensor reindex contract)
end G
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor_denote reindex_denote)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))

def pure (p q : K) : Signature K 4:=fun x=>
  if x=(fun _=>false) then p else if x=(fun _=>true) then q else 0

def order : Equiv.Perm (Fin 6) where
  toFun:=![4,5,0,2,1,3]
  invFun:=![2,4,3,5,0,1]
  left_inv:=by decide
  right_inv:=by decide

theorem order_value (f : Signature K 4) (g : Signature K 2) :
    Tensor.reindex order (Signature.tensor f g)=fun x=>f ![x 4,x 5,x 0,x 2]*g ![x 1,x 3] := by
  funext x
  apply congrArg₂ (· * ·)
  · apply congrArg f
    funext i
    fin_cases i <;> rfl
  · apply congrArg g
    funext i
    fin_cases i <;> rfl

theorem const_two (v : Bool) : (![v,v] : Fin 2→Bool)=(fun _=>v) := by
  funext i
  fin_cases i <;> rfl

def cap (Q : O.Output H 4) (B : O.Output H 2) : O.Output H 2:=
  G.contract H (G.contract H (G.reindex H (G.tensor H Q B) order))

theorem cap_value (Q : O.Output H 4) (B : O.Output H 2) (p q : K)
    (form : Q.network.denote=pure p q) :
    (cap H Q B).network.denote=binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal
      (p*B.network.denote (fun _=>true)) (q*B.network.denote (fun _=>false))) := by
  change (((Holant.Complexity.BinaryInterpolation.Chains.reindex
    (Holant.Complexity.BinaryInterpolation.Chains.tensor Q.network B.network) order).contract
      Signature.disequality).contract Signature.disequality).denote = _
  rw [Network.denote_contract,Network.denote_contract,C.reindex_denote,C.tensor_denote,form,order_value]
  funext x
  change (∑i : Bool,∑j : Bool,Signature.disequality i j *
    (∑k : Bool,∑l : Bool,Signature.disequality k l * (pure p q ![x 0,x 1,k,i]*B.network.denote ![l,j])))=_
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [pure,Signature.disequality,binarySignature,OrdinaryTargetInterpolationDiagonal.diagonal,
      funext_iff,Fin.forall_fin_succ,h0,h1,const_two]

/-- A full unary supplies the binary diagonal cofactor by two actual copies. -/
def unaryCap (Q : O.Output H 4) (U : O.Output H 1) : O.Output H 2:=cap H Q (G.tensor H U U)

theorem unary_value (Q : O.Output H 4) (U : O.Output H 1) (p q : K)
    (form : Q.network.denote=pure p q) :
    (unaryCap H Q U).network.denote=binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal
      (p*(U.network.denote (fun _=>true))^2) (q*(U.network.denote (fun _=>false))^2)) := by
  rw [unaryCap,cap_value H Q (G.tensor H U U) p q form]
  change binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal
      (p*(Holant.Complexity.BinaryInterpolation.Chains.tensor U.network U.network).denote (fun _=>true))
      (q*(Holant.Complexity.BinaryInterpolation.Chains.tensor U.network U.network).denote (fun _=>false)))=_
  rw [C.tensor_denote]
  simp [Signature.tensor_apply,pow_two]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureEqualityCap
end
