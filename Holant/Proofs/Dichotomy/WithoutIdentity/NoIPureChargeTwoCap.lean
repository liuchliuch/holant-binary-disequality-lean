import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoCapPorts

/-! Actual four-edge native cap against pure Eq4. Every input occurrence
keeps its original label and both pure endpoint multipliers remain exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoCap
open Holant Holant.Complexity
namespace G
export GlobalCloseCompletionComplementQ4Templates (tensor reindex contract)
end G
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor_denote reindex_denote)
end C
namespace P
export NoIPureChargeTwoCapPorts (order old row equality)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))

theorem order_value (f : Signature K (n+4)) (g : Signature K 4) :
    Tensor.reindex (P.order n) (Signature.tensor (m:=n+4) (n:=4) f g)=fun x=>
      f (Fin.append (fun i : Fin n=>x ⟨i.val+8,by omega⟩) ![x 0,x 2,x 4,x 6]) *
        g ![x 1,x 3,x 5,x 7] := by
  funext x
  apply congrArg₂ (· * ·)
  · apply congrArg f
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · rw [Fin.append_left]
      change x (P.order n (Fin.castAdd 8 j))=x ⟨j.val+8,by omega⟩
      rw [P.old]
      exact congrArg x (Fin.ext (Nat.add_comm 8 j.val))
    · rw [Fin.append_right]
      change x (P.order n ⟨n+j.val,by omega⟩)=_
      rw [P.row]
      fin_cases j <;> rfl
  · apply congrArg g
    funext i
    change x (P.order n ⟨n+4+i.val,by omega⟩)=_
    rw [P.equality]
    fin_cases i <;> rfl

def cap (N : NativeAntiTargetSource.Output H (n+4)) (Q : NativeAntiTargetSource.Output H 4) :
    NativeAntiTargetSource.Output H n :=
  G.contract H (n:=n) (G.contract H (n:=n+2) (G.contract H (n:=n+4) (G.contract H (n:=n+6)
    (G.reindex H (n:=n+8) (G.tensor H (m:=n+4) (n:=4) N Q) (P.order n)))))

theorem value (N : NativeAntiTargetSource.Output H (n+4)) (Q : NativeAntiTargetSource.Output H 4)
    (p q : K) (form : Q.network.denote=NoIPureEqualityCap.pure p q) :
    (cap H N Q).network.denote=fun x=>
      p*N.network.denote (Fin.append x (fun _ : Fin 4=>true))+
      q*N.network.denote (Fin.append x (fun _ : Fin 4=>false)) := by
  change (((((Holant.Complexity.BinaryInterpolation.Chains.reindex
    (Holant.Complexity.BinaryInterpolation.Chains.tensor (m:=n+4) (n:=4) N.network Q.network) (P.order n)).contract
      Signature.disequality).contract Signature.disequality).contract Signature.disequality).contract
      Signature.disequality).denote=_
  rw [Network.denote_contract,Network.denote_contract,Network.denote_contract,Network.denote_contract,
    C.reindex_denote,C.tensor_denote,form,order_value]
  funext x
  change (∑i : Bool,∑j : Bool,Signature.disequality i j *
    (∑k : Bool,∑l : Bool,Signature.disequality k l *
      (∑m : Bool,∑v : Bool,Signature.disequality m v *
        (∑r : Bool,∑t : Bool,Signature.disequality r t *
          (N.network.denote (Fin.append x ![r,m,k,i])*NoIPureEqualityCap.pure p q ![t,v,l,j])))))=_
  have constant (b : Bool) : (![b,b,b,b] : Fin 4→Bool)=(fun _=>b) := by
    funext i;fin_cases i <;> rfl
  simp [NoIPureEqualityCap.pure,Signature.disequality,
    funext_iff,Fin.forall_fin_succ,constant,mul_comm,add_comm]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoCap
end
