import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddRaw

/-! A temporary constant-one unary label records the boundary sites of the
closed auxiliary compiler. Its only occurrences are subsequently replaced
by Eq4 terminals; it is never supplied to an original-oracle reduction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTable
open Holant Holant.Tractable Holant.Complexity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))
abbrev arity := NoXGeneralOddRaw.arity (s:=s) (a:=a)

def table (j : Fin (s+1)) : Signature K (arity (s:=s) (a:=a) j.val) := fun x=>
  if h : j.val<s then H ⟨j.val,h⟩ (fun i=>x ⟨i.val,by simpa only [arity,NoXGeneralOddRaw.arity,ite_eq_left h] using i.isLt⟩) else 1

def old (j : Fin s) : Fin (s+1) := Fin.castAdd 1 j

def marked : Fin (s+1) := ⟨s,Nat.lt_succ_self _⟩

omit [Field K] in
private theorem literal_cast {m t : ℕ} (f : Signature K m) (h : m=t) :
    (⟨m,f⟩ : AnySignature K)=⟨t,fun x=>f (fun i=>x (Fin.cast h i))⟩ := by cases h;rfl

theorem old_literal (j : Fin s) :
    (⟨arity (s:=s) (a:=a) (old j).val,table H (old j)⟩ : AnySignature K)=⟨a j.val,H j⟩ := by
  have ar : a j.val=arity (s:=s) (a:=a) (old j).val := by simp [arity,NoXGeneralOddRaw.arity,old,j.isLt]
  have row : table H (old j)=fun x=>H j (fun i=>x (Fin.cast ar i)) := by
    funext x
    simp only [table,old,Fin.val_castAdd,dite_eq_left j.isLt]
    rfl
  rw [row]
  exact (literal_cast (H j) ar).symm

theorem marked_literal : (⟨arity (s:=s) (a:=a) (marked (s:=s)).val,table H marked⟩ : AnySignature K)=⟨1,fun _=>1⟩ := by
  have ar : 1=arity (s:=s) (a:=a) (marked (s:=s)).val := by simp [arity,NoXGeneralOddRaw.arity,marked]
  have row : table H marked=fun _=>1 := by funext x;simp [table,marked]
  rw [row]
  exact (literal_cast (fun _ : Fin 1→Bool=>(1 : K)) ar).symm

theorem old_value (j : Fin (s+1)) (hj : j.val<s) (x : Fin (arity (s:=s) (a:=a) j.val)→Bool) :
    table H j x=H ⟨j.val,hj⟩ (fun i=>x ⟨i.val,by simpa only [arity,NoXGeneralOddRaw.arity,ite_eq_left hj] using i.isLt⟩) := by
  simp only [table,dite_eq_left hj]

theorem marked_value (x : Fin (arity (s:=s) (a:=a) (marked (s:=s)).val)→Bool) : table H marked x=1 := by
  simp [table,marked]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTable
end
