import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureEqualityCap

/-! Three literal native-X joins turn a pure odd ternary and a pure
quaternary into a full unary. All source vertices and scalar factors remain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddTriple
open Holant Holant.Complexity
open scoped BigOperators
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
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))

def pure (a b : K) : Signature K 3:=fun x=>
  if x=(fun _=>false) then a else if x=(fun _=>true) then b else 0

def order : Equiv.Perm (Fin 7) where
  toFun:=![0,2,4,1,3,5,6]
  invFun:=![0,3,1,4,2,5,6]
  left_inv:=by decide
  right_inv:=by decide

theorem order_value (f : Signature K 3) (g : Signature K 4) :
    Tensor.reindex order (Signature.tensor f g)=
      fun x=>f ![x 0,x 2,x 4]*g ![x 1,x 3,x 5,x 6] := by
  funext x
  apply congrArg₂ (· * ·)
  · apply congrArg f
    funext i
    fin_cases i <;> rfl
  · apply congrArg g
    funext i
    fin_cases i <;> rfl

def output (R : O.Output H 3) (Q : O.Output H 4) : O.Output H 1:=
  G.contract H (n:=1) (G.contract H (n:=3) (G.contract H (n:=5)
    (G.reindex H (n:=7) (G.tensor H (m:=3) (n:=4) R Q) order)))

theorem value (R : O.Output H 3) (Q : O.Output H 4) (a b p q : K)
    (rform : R.network.denote=pure a b)
    (qform : Q.network.denote=NoIPureEqualityCap.pure p q) :
    (output H R Q).network.denote=fun x=>if x 0 then a*q else b*p := by
  change ((((Holant.Complexity.BinaryInterpolation.Chains.reindex
    (Holant.Complexity.BinaryInterpolation.Chains.tensor R.network Q.network) order).contract
      Signature.disequality).contract Signature.disequality).contract Signature.disequality).denote = _
  rw [Network.denote_contract,Network.denote_contract,Network.denote_contract,
    C.reindex_denote,C.tensor_denote,rform,qform,order_value]
  funext x
  change (∑i : Bool,∑j : Bool,Signature.disequality i j *
    (∑k : Bool,∑l : Bool,Signature.disequality k l *
      (∑m : Bool,∑n : Bool,Signature.disequality m n *
        (pure a b ![m,k,i]*NoIPureEqualityCap.pure p q ![n,l,j,x 0]))))=_
  cases hx:x 0 <;> simp [pure,NoIPureEqualityCap.pure,Signature.disequality,
    funext_iff,Fin.forall_fin_succ,hx]

theorem full (R : O.Output H 3) (Q : O.Output H 4) (a b p q : K)
    (an : a≠0) (bn : b≠0) (pn : p≠0) (qn : q≠0)
    (rform : R.network.denote=pure a b)
    (qform : Q.network.denote=NoIPureEqualityCap.pure p q) :
    (output H R Q).network.denote (fun _=>false)≠0 ∧
      (output H R Q).network.denote (fun _=>true)≠0 := by
  rw [value H R Q a b p q rform qform]
  exact ⟨mul_ne_zero bn pn,mul_ne_zero an qn⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddTriple
end
