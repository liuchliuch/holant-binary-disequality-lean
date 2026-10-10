import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureEqualityCap

/-! A fixed native cap joins the last four ports of the actual source row
to the four ports of pure equality. The surviving prefix keeps its order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoCapPorts
open Holant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false

def forward (n : ℕ) (i : Fin (n+8)) : Fin (n+8) :=
  if h : i.val<n then ⟨8+i.val,by omega⟩
  else if h4 : i.val<n+4 then ⟨2*(i.val-n),by omega⟩
  else ⟨2*(i.val-(n+4))+1,by omega⟩

def backward (n : ℕ) (i : Fin (n+8)) : Fin (n+8) :=
  if h : i.val<8 then
    if even : i.val%2=0 then ⟨n+i.val/2,by omega⟩
    else ⟨n+4+i.val/2,by omega⟩
  else ⟨i.val-8,by omega⟩

def order (n : ℕ) : Equiv.Perm (Fin (n+8)) where
  toFun:=forward n
  invFun:=backward n
  left_inv:=by
    intro i
    apply Fin.ext
    by_cases h : i.val<n
    · simp [forward,h,backward,show ¬8+i.val<8 by omega]
    · by_cases h4 : i.val<n+4
      · have small : 2*(i.val-n)<8:=by omega
        simp [forward,h,h4,backward,small]
        omega
      · have small : 2*(i.val-(n+4))+1<8:=by omega
        simp [forward,h,h4,backward,small]
        omega
  right_inv:=by
    intro i
    apply Fin.ext
    by_cases h : i.val<8
    · by_cases even : i.val%2=0
      · have lo : ¬n+i.val/2<n:=by omega
        have hi : n+i.val/2<n+4:=by omega
        simp [backward,h,even,forward,lo,hi]
        omega
      · have lo : ¬n+4+i.val/2<n:=by omega
        have hi : ¬n+4+i.val/2<n+4:=by omega
        simp [backward,h,even,forward,lo,hi]
        omega
    · have lo : i.val-8<n:=by omega
      simp [backward,h,forward,lo]
      omega

theorem old (n : ℕ) (i : Fin n) :
    order n (Fin.castAdd 8 i)=⟨8+i.val,by omega⟩ := by
  simp [order,forward,i.isLt]

theorem row (n : ℕ) (i : Fin 4) :
    order n ⟨n+i.val,by omega⟩=⟨2*i.val,by omega⟩ := by
  simp [order,forward,show ¬n+i.val<n by omega,show n+i.val<n+4 by omega]

theorem equality (n : ℕ) (i : Fin 4) :
    order n ⟨n+4+i.val,by omega⟩=⟨2*i.val+1,by omega⟩ := by
  simp [order,forward,show ¬n+4+i.val<n by omega,show ¬n+4+i.val<n+4 by omega]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoCapPorts
end
