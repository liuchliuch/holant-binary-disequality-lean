import Holant.Support
import Holant.EightVertex.ProductAnchor.NetworksData

/-! Scalar-one signed equality coefficients, independent of graph sources. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeSigned
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}
namespace A
def leftWord (x : Fin (n+3) → Bool) : Fin n → Bool := fun i => x (Fin.castAdd 3 i)
def rightWord (x : Fin (n+3) → Bool) : Fin 3 → Bool := fun i => x (Fin.natAdd n i)
end A
def row (w : Fin n→Bool) : Signature K n:=fun x=>
  (if x=w then 1 else 0)+(if x=(fun i=> !(w i)) then 1 else 0)

theorem not_cons (b : Bool) (w : Fin n→Bool) :
    (fun i : Fin (n+1)=> !((Fin.cons b w : Fin (n+1)→Bool) i))=Fin.cons (!b) (fun i=> !(w i)) := by
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

theorem not_append (w : Fin n→Bool) (v : Fin 3→Bool) :
    (fun i=> !(Fin.addCases w v i))=Fin.addCases (fun i=> !(w i)) (fun i=> !(v i)) := by
  funext i
  obtain ⟨j,rfl⟩:=(finSumFinEquiv : Fin n⊕Fin 3≃Fin (n+3)).surjective i
  cases j <;> simp

theorem append_eq (x : Fin (n+3)→Bool) (w : Fin n→Bool) (v : Fin 3→Bool) :
    x=Fin.addCases w v ↔ A.leftWord x=w ∧ A.rightWord x=v := by
  constructor
  · rintro rfl
    constructor <;> funext i <;> simp [A.leftWord,A.rightWord]
  · rintro ⟨hL,hR⟩
    funext i
    obtain ⟨j,rfl⟩:=(finSumFinEquiv : Fin n⊕Fin 3≃Fin (n+3)).surjective i
    cases j with
    | inl j=>simpa [A.leftWord] using congrFun hL j
    | inr j=>simpa [A.rightWord] using congrFun hR j

theorem row_append (x : Fin (n+3)→Bool) (w : Fin n→Bool) (v : Fin 3→Bool) :
    row (K:=K) (Fin.addCases w v) x=
      (if A.leftWord x=w ∧ A.rightWord x=v then 1 else 0)+
      (if A.leftWord x=(fun i=> !(w i)) ∧ A.rightWord x=(fun i=> !(v i)) then 1 else 0) := by
  simp only [row,not_append,append_eq]

theorem row_cons (x w : Fin n→Bool) (a b : Bool) :
    row (K:=K) (Fin.cons b w) (Fin.cons a x)=
      (if a=b ∧ x=w then 1 else 0)+(if a= !b ∧ x=(fun i=> !(w i)) then 1 else 0) := by
  simp only [row,not_cons,Fin.cons_inj]

theorem eq4_cons (x : Fin 3→Bool) (b : Bool) :
    (Holant.EightVertex.ProductAnchor.equalityFour (Fin.cons b x) : K)=if x=(fun _=>b) then 1 else 0 := by
  have cond : (∀i : Fin 4,(Fin.cons b x : Fin 4→Bool) i=b) ↔ x=(fun _=>b) := by
    rw [Fin.forall_fin_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,eq_self_iff_true,true_and]
    exact funext_iff.symm
  change (if ∀i : Fin 4,(Fin.cons b x : Fin 4→Bool) i=b then 1 else 0)=_
  simp only [cond]


theorem reindex (w : Fin n→Bool) (e : Equiv.Perm (Fin n)) :
    Tensor.reindex e (row (K:=K) w)=row (fun i=>w (e.symm i)) := by
  funext x
  have eqv (v : Fin n→Bool) : (fun i=>x (e i))=v ↔ x=(fun i=>v (e.symm i)) := by
    constructor
    · intro h;funext i;simpa using congrFun h (e.symm i)
    · rintro rfl;funext i;simp
  simp only [Tensor.reindex,row,eqv]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeSigned
end
