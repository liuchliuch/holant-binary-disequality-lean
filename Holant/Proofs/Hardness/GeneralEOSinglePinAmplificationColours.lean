import Holant.Proofs.Hardness.ExactTwoReferenceColours

/-! The anchored reference cycle has exactly one surviving colour assignment.
No symmetry of the original signatures is used, and the empty source-pin list
is covered by the same formula. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationColours
open Holant
open scoped BigOperators
namespace C
export ExactTwoReferenceColours (factor factor_constant factor_mismatch pinValue)
end C
variable {K : Type*} [Field K]

def anchor (a b : Bool) : K := if a=false ∧ b=false then 1 else 0

def weight {m : ℕ} (A B : Fin m → Bool) (y : Fin (m+1) → Bool) : K :=
  anchor (y (Fin.last m)) (y 0)*∏i : Fin m,
    C.factor (A i) (B i) (y i.castSucc) (y i.succ)

theorem weight_false {m : ℕ} (A B : Fin m → Bool) :
    weight (K:=K) A B (fun _ => false)=∏i,C.pinValue false (A i) (B i) := by
  simp only [weight,anchor,and_self,ite_true,one_mul,C.factor_constant]

theorem constant_of_weight_ne_zero {m : ℕ} (A B : Fin m → Bool)
    (y : Fin (m+1) → Bool) (h : weight (K:=K) A B y≠0) : y=fun _ => false := by
  have ha : anchor (K:=K) (y (Fin.last m)) (y 0)≠0 := left_ne_zero_of_mul h
  have hz : y 0=false := by
    unfold anchor at ha
    split_ifs at ha with he
    · exact he.2
    · exact False.elim (ha rfl)
  have hp : (∏i : Fin m,C.factor (K:=K) (A i) (B i) (y i.castSucc) (y i.succ))≠0 :=
    right_ne_zero_of_mul h
  have hs (i : Fin m) : y i.castSucc=y i.succ := by
    by_contra hn
    exact (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _))
      (C.factor_mismatch _ _ _ _ hn)
  have aux : ∀n (hn : n<m+1),y ⟨n,hn⟩=false := by
    intro n
    induction n with
    | zero => intro hn; exact hz
    | succ n ih =>
      intro hn
      have hh := hs ⟨n,by omega⟩
      exact hh.symm.trans (ih (by omega))
  funext i
  exact aux i.val i.isLt

theorem sum_colours {m : ℕ} (A B : Fin m → Bool) :
    (∑y : Fin (m+1) → Bool,weight (K:=K) A B y)=
      ∏i,C.pinValue false (A i) (B i) := by
  classical
  rw [←weight_false A B]
  apply Finset.sum_eq_single (fun _ => false)
  · intro y _ hy
    by_contra hn
    exact hy (constant_of_weight_ne_zero A B y hn)
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationColours
