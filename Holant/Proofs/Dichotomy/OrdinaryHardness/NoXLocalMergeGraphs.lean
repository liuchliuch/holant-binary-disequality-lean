import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! Literal Eq4 merges retain two exposed copies of the merged variable.
Both input ports are wired to one actual Eq4 vertex, so their equality is
imposed while support rank can decrease. A weighted opposite merge first
uses one actual antidiagonal edge; no XOR or compressed row is free. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalMergeGraphs
open Holant Holant.Tractable
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro
  (row tensor reindex contract row_denote tensor_denote reindex_denote contract_denote)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def orderVal (n k : ℕ) : ℕ :=
  if k=0 then 0 else if k=1 then 2 else if k<n+2 then k+4
  else if k=n+2 then 1 else if k=n+3 then 3 else if k=n+4 then 4 else 5

def inverseVal (n k : ℕ) : ℕ :=
  if k=0 then 0 else if k=1 then n+2 else if k=2 then 1
  else if k=3 then n+3 else if k=4 then n+4 else if k=5 then n+5 else k-4

private theorem inverse_order_val (n k : ℕ) (hk : k<n+6) : inverseVal n (orderVal n k)=k := by
  by_cases h0 : k=0
  · subst k;simp [orderVal,inverseVal]
  by_cases h1 : k=1
  · subst k;simp [orderVal,inverseVal]
  by_cases hs : k<n+2
  · simp only [orderVal,ite_eq_right h0,ite_eq_right h1,ite_eq_left hs]
    unfold inverseVal
    split_ifs <;> simp_all only [Nat.add_sub_cancel] <;> omega
  by_cases h2 : k=n+2
  · simp [orderVal,h2,inverseVal]
  by_cases h3 : k=n+3
  · simp [orderVal,h3,inverseVal]
  by_cases h4 : k=n+4
  · simp [orderVal,h4,inverseVal]
  have h5 : k=n+5 := by omega
  simp [orderVal,inverseVal,h5]

private theorem order_inverse_val (n k : ℕ) (hk : k<n+6) : orderVal n (inverseVal n k)=k := by
  by_cases h0 : k=0
  · subst k;simp [orderVal,inverseVal]
  by_cases h1 : k=1
  · subst k;norm_num [orderVal,inverseVal]
  by_cases h2 : k=2
  · subst k;norm_num [orderVal,inverseVal]
  by_cases h3 : k=3
  · subst k;norm_num [orderVal,inverseVal]
  by_cases h4 : k=4
  · subst k;norm_num [orderVal,inverseVal]
  by_cases h5 : k=5
  · subst k;norm_num [orderVal,inverseVal]
  simp only [inverseVal,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,
    ite_eq_right h3,ite_eq_right h4,ite_eq_right h5]
  unfold orderVal
  split_ifs <;> omega

def order (n : ℕ) : Equiv.Perm (Fin (n+6)) where
  toFun i := ⟨orderVal n i.val,by have h:=i.isLt;unfold orderVal;split_ifs <;> omega⟩
  invFun i := ⟨inverseVal n i.val,by have h:=i.isLt;unfold inverseVal;split_ifs <;> omega⟩
  left_inv i := Fin.ext (inverse_order_val n i.val i.isLt)
  right_inv i := Fin.ext (order_inverse_val n i.val i.isLt)

variable {n : ℕ}
def tail (x : Fin (n+2)→Bool) : Fin n→Bool := fun i=>x i.succ.succ

def assignment (a b : Bool) (x : Fin (n+2)→Bool) : Fin (n+6)→Bool :=
  Fin.cons a (Fin.cons a (Fin.cons b (Fin.cons b x)))

theorem left_assignment (a b : Bool) (x : Fin (n+2)→Bool) (i : Fin (n+2)) :
    assignment a b x (order n (Fin.castAdd 4 i))=((Fin.cons a (Fin.cons b (tail x)) : Fin (n+2)→Bool) i) := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun j=>?_) i) i
  · have h : order n (Fin.castAdd 4 (0 : Fin (n+2)))=⟨0,by omega⟩ := by
      apply Fin.ext
      change orderVal n 0=0
      rfl
    rw [h]
    rfl
  · have h : order n (Fin.castAdd 4 (Fin.succ (0 : Fin (n+1))))=⟨2,by omega⟩ := by
      apply Fin.ext
      change orderVal n 1=2
      rfl
    rw [h]
    rfl
  · have h : order n (Fin.castAdd 4 j.succ.succ)=j.succ.succ.succ.succ.succ.succ := by
      apply Fin.ext
      change orderVal n (j.val+1+1)=j.val+1+1+1+1+1+1
      have hj:=j.isLt
      unfold orderVal
      split_ifs <;> omega
    rw [h]
    rfl

theorem right_assignment (a b : Bool) (x : Fin (n+2)→Bool) (i : Fin 4) :
    assignment a b x (order n (Fin.natAdd (n+2) i))=![a,b,x 0,x 1] i := by
  have hp : order n (Fin.natAdd (n+2) i)=(![⟨1,by omega⟩,⟨3,by omega⟩,⟨4,by omega⟩,⟨5,by omega⟩] : Fin 4→Fin (n+6)) i := by
    apply Fin.ext
    fin_cases i
    · change orderVal n (n+2+0)=1
      unfold orderVal;split_ifs <;> omega
    · change orderVal n (n+2+1)=3
      unfold orderVal;split_ifs <;> omega
    · change orderVal n (n+2+2)=4
      unfold orderVal;split_ifs <;> omega
    · change orderVal n (n+2+3)=5
      unfold orderVal;split_ifs <;> omega
  rw [hp]
  fin_cases i <;> rfl

def swapPorts : Equiv.Perm (Fin (2+(n+2))) := Equiv.swap ⟨1,by omega⟩ ⟨2,by omega⟩

def flipIndex (i : Fin (2+(n+2))) : Fin ((n+2)+2) :=
  Fin.cast (by omega : 2+(n+2)=(n+2)+2) (swapPorts i)

theorem flip_left (t : Bool) (x : Fin (n+2)→Bool) (i : Fin 2) :
    ((Fin.cons t (Fin.cons t x)) : Fin ((n+2)+2)→Bool) (flipIndex (Fin.castAdd (n+2) i))=![t,x 0] i := by
  have hp : flipIndex (Fin.castAdd (n+2) i)=(![⟨0,by omega⟩,⟨2,by omega⟩] : Fin 2→Fin ((n+2)+2)) i := by
    fin_cases i
    · apply Fin.ext
      simp only [flipIndex,swapPorts,Equiv.swap_apply_def,Fin.val_cast]
      split_ifs with h1 h2
      · have hh:=congrArg Fin.val h1
        norm_num at hh
      · have hh:=congrArg Fin.val h2
        norm_num at hh
      · rfl
    · change flipIndex (⟨1,by omega⟩ : Fin (2+(n+2)))=⟨2,by omega⟩
      rw [flipIndex,swapPorts,Equiv.swap_apply_left]
      rfl
  rw [hp]
  fin_cases i <;> rfl

theorem flip_right (t : Bool) (x : Fin (n+2)→Bool) (i : Fin (n+2)) :
    ((Fin.cons t (Fin.cons t x)) : Fin ((n+2)+2)→Bool) (flipIndex (Fin.natAdd 2 i))=
      (Fin.cons t (fun j=>x j.succ) : Fin (n+2)→Bool) i := by
  refine Fin.cases ?_ (fun j=>?_) i
  · have hp : flipIndex (Fin.natAdd 2 (0 : Fin (n+2)))=⟨1,by omega⟩ := by
      have he : Fin.natAdd 2 (0 : Fin (n+2))=(⟨2,by omega⟩ : Fin (2+(n+2))) := rfl
      rw [flipIndex,swapPorts,he,Equiv.swap_apply_right]
      rfl
    rw [hp]
    rfl
  · have hp : flipIndex (Fin.natAdd 2 j.succ)=j.succ.succ.succ := by
      apply Fin.ext
      have h1 : Fin.natAdd 2 j.succ≠(⟨1,by omega⟩ : Fin (2+(n+2))) := by
        intro he
        have hh:=congrArg Fin.val he
        change 2+(j.val+1)=1 at hh
        omega
      have h2 : Fin.natAdd 2 j.succ≠(⟨2,by omega⟩ : Fin (2+(n+2))) := by
        intro he
        have hh:=congrArg Fin.val he
        change 2+(j.val+1)=2 at hh
        omega
      simp only [flipIndex,swapPorts,Equiv.swap_apply_def,ite_eq_right h1,ite_eq_right h2,Fin.val_cast,Fin.val_natAdd,Fin.val_succ]
      omega
    rw [hp]
    rfl

variable {K : Type} [Field K] {s : ℕ} {arity : ℕ→ℕ}
variable {H : (j : Fin s)→Signature K (arity j.val)}
def cast {k l : ℕ} (N : M.Macro H k) (h : k=l) : M.Macro H l := h ▸ N

theorem cast_denote {k l : ℕ} (N : M.Macro H k) (h : k=l) (x : Fin l→Bool) :
    (cast N h).network.denote x=N.network.denote (fun i=>x (Fin.cast h i)) := by
  subst l
  rfl

variable (N : M.Macro H (n+2)) (E : M.Macro H 4)

def equalMerge : M.Macro H (n+2) := ((N.tensor E).reindex (order n)).contract.contract

theorem reindexed_value (a b : Bool) (x : Fin (n+2)→Bool) :
    ((N.tensor E).reindex (order n)).network.denote (assignment a b x)=
      N.network.denote (Fin.cons a (Fin.cons b (tail x)))*E.network.denote ![a,b,x 0,x 1] := by
  rw [M.reindex_denote,M.tensor_denote]
  unfold Tensor.reindex
  rw [Signature.tensor_apply]
  congr 1
  · exact congrArg N.network.denote (funext (left_assignment a b x))
  · exact congrArg E.network.denote (funext (right_assignment a b x))

variable (eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour)
include eq4 in
theorem equalMerge_value (x : Fin (n+2)→Bool) :
    (equalMerge N E).network.denote x=if x 0=x 1 then N.network.denote x else 0 := by
  rw [equalMerge,M.contract_denote]
  simp only [M.contract_denote]
  change ((N.tensor E).reindex (order n)).network.denote (assignment false false x)+
      ((N.tensor E).reindex (order n)).network.denote (assignment true false x)+
      (((N.tensor E).reindex (order n)).network.denote (assignment false true x)+
      ((N.tensor E).reindex (order n)).network.denote (assignment true true x))=_
  rw [reindexed_value,reindexed_value,reindexed_value,reindexed_value,eq4]
  have word : Fin.cons (x 0) (Fin.cons (x 1) (tail x))=x := by
    funext i
    refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun j=>?_) i) i <;> rfl
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ,h0,h1] at word ⊢
  all_goals rw [word]

variable (A : M.Macro H 2) (v w : K)
variable (anti : A.network.denote=NoXWeightedAntiSigned.anti v w)

def flipFirst : M.Macro H (n+2) :=
  (cast ((A.tensor N).reindex swapPorts) (by omega : 2+(n+2)=(n+2)+2)).contract

include anti in
theorem flipFirst_value (x : Fin (n+2)→Bool) :
    (flipFirst N A).network.denote x=(if x 0 then v else w)*
      N.network.denote (Fin.cons (!(x 0)) (fun i=>x i.succ)) := by
  have eval (t : Bool) :
      (cast ((A.tensor N).reindex swapPorts) (by omega : 2+(n+2)=(n+2)+2)).network.denote
        ((Fin.cons t (Fin.cons t x)) : Fin ((n+2)+2)→Bool)=
      NoXWeightedAntiSigned.anti v w ![t,x 0]*N.network.denote (Fin.cons t (fun i=>x i.succ)) := by
    rw [cast_denote,M.reindex_denote,M.tensor_denote,anti]
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    change (NoXWeightedAntiSigned.anti v w (fun i=>((Fin.cons t (Fin.cons t x)) : Fin ((n+2)+2)→Bool) (flipIndex (Fin.castAdd (n+2) i))))*
      N.network.denote (fun i=>((Fin.cons t (Fin.cons t x)) : Fin ((n+2)+2)→Bool) (flipIndex (Fin.natAdd 2 i)))=_
    rw [funext (flip_left t x),funext (flip_right t x)]
  rw [flipFirst,M.contract_denote,eval,eval]
  cases x 0 <;> simp [NoXWeightedAntiSigned.anti]

def oppositeMerge : M.Macro H (n+2) := equalMerge (flipFirst N A) E

include eq4 anti in
theorem oppositeMerge_value (x : Fin (n+2)→Bool) :
    (oppositeMerge N E A).network.denote x=if x 0=x 1 then
      (if x 0 then v else w)*N.network.denote (Fin.cons (!(x 0)) (fun i=>x i.succ)) else 0 := by
  rw [oppositeMerge,equalMerge_value _ E eq4,flipFirst_value N A v w anti]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalMergeGraphs
end
