import Holant.Proofs.Hardness.ExactTwoReferenceValidation
import Holant.Proofs.Hardness.ExactTwoSignatures

/-! Exact elimination of the fresh ring colours.
These are finite semantic sums, not a polynomial-time enumeration algorithm.
For a nonempty ring its actual E/X constraints leave precisely the two constant
reference colours. Arbitrarily correlated old endpoint bits remain untouched. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceColours
open Holant
open ExactTwoReferenceRaw ExactTwoReferenceValidation
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

/-- Under native Choice.bit, true-end=y and false-end=!y. -/
def factor (a b s t : Bool) : K := ExactTwoSignatures.E ![a,b,s,!t]
def pinValue (phase a b : Bool) : K := if a=phase ∧ b=!phase then 1 else 0

theorem factor_constant (a b phase : Bool) :
    factor (K:=K) a b phase phase=pinValue phase a b := by
  cases a <;> cases b <;> cases phase <;>
    simp [factor,ExactTwoSignatures.E_reference,pinValue]

theorem factor_mismatch (a b s t : Bool) (h : s≠t) : factor (K:=K) a b s t=0 := by
  cases a <;> cases b <;> cases s <;> cases t <;>
    simp_all [factor,ExactTwoSignatures.E_reference]

/-- The explicit predecessor edges propagate one reference value through all
indices. This proves connectedness of the actual cycle, rather than assuming it. -/
theorem all_eq_zero {m : ℕ} (hm : 0<m) (y : Fin m → Bool)
    (h : ∀i,y (previousFin i)=y i) (i : Fin m) : y i=y ⟨0,hm⟩ := by
  have aux : ∀n (hn : n<m),y ⟨n,hn⟩=y ⟨0,hm⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
        intro hn
        have hp := h ⟨n+1,hn⟩
        have hp' : y ⟨n,by omega⟩=y ⟨n+1,hn⟩ := by
          simpa only [previousFin,previous,Nat.add_eq_zero_iff,one_ne_zero,and_false,
            ite_false,Nat.add_sub_cancel] using hp
        exact hp'.symm.trans (ih (by omega))
  exact aux i.val i.isLt

def weight {m : ℕ} (A B y : Fin m → Bool) : K :=
  ∏i,factor (A i) (B i) (y (previousFin i)) (y i)

theorem weight_constant {m : ℕ} (A B : Fin m → Bool) (phase : Bool) :
    weight (K:=K) A B (fun _=>phase)=∏i,pinValue phase (A i) (B i) := by
  simp only [weight,factor_constant]

 theorem weight_zero_of_notconstant {m : ℕ} (hm : 0<m) (A B y : Fin m → Bool)
    (hy : ∀phase : Bool,y≠fun _=>phase) : weight (K:=K) A B y=0 := by
  classical
  have he : ∃i,y (previousFin i)≠y i := by
    by_contra h
    push_neg at h
    apply hy (y ⟨0,hm⟩)
    funext i
    exact all_eq_zero hm y h i
  obtain ⟨i,hi⟩ := he
  unfold weight
  exact Finset.prod_eq_zero (Finset.mem_univ i) (factor_mismatch _ _ _ _ hi)

/-- Full m>0 ring sum: precisely all01 and all10, each once. -/
theorem sum_colours {m : ℕ} (hm : 0<m) (A B : Fin m → Bool) :
    (∑y : Fin m → Bool,weight (K:=K) A B y)=
      (∏i,pinValue false (A i) (B i))+(∏i,pinValue true (A i) (B i)) := by
  classical
  let constant : Bool → Fin m → Bool := fun b _=>b
  have hi : Function.Injective constant := by
    intro a b h
    exact congrFun h ⟨0,hm⟩
  have hsum : (∑y : Fin m → Bool,weight (K:=K) A B y)=
      ∑y∈Finset.univ.image constant,weight (K:=K) A B y := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    apply weight_zero_of_notconstant hm
    intro phase h
    apply hy
    exact Finset.mem_image.mpr ⟨phase,Finset.mem_univ _,h.symm⟩
  rw [hsum,Finset.sum_image]
  · simp only [constant,weight_constant,Fintype.sum_bool]
    all_goals exact add_comm _ _
  · intro a _ b _ h
    exact hi h

/-- The empty reference domain has one empty assignment, not two phases. -/
theorem sum_empty (A B : Fin 0 → Bool) : (∑y : Fin 0 → Bool,weight (K:=K) A B y)=1 := by
  simp [weight]

end
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceColours
