import Holant.Certificates.FourthRootOdd.Parity
import Holant.Certificates.TwelveLoops.Source

/-! Every actual normalized fourth-root odd table is represented by the exact
seven-exponent state space. This closes the interface from coefficients to the
finite certificate; callers do not supply an enumeration-membership premise. -/
noncomputable section
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops

def NormalizedOdd (f : Signature ℂ 4) : Prop :=
  f (singleWord 0)=1 ∧ (∀ x,evenWord x=true → f x=0) ∧
    ∀ j : Fin 4,f (singleWord j)^4=1 ∧ f (complementWord j)^4=1

theorem fourth_power_code {z : ℂ} (h : z^4=1) : ∃ k : Fin 4,embed (fourthRoot k)=z := by
  have hs : (z^2)^2=1 := by simpa only [←pow_mul] using h
  rcases sq_eq_one_iff.mp hs with hp | hn
  · rcases sq_eq_one_iff.mp hp with hz | hz
    · exact ⟨0,by simp [fourthRoot,embed,hz]⟩
    · exact ⟨2,by simp [fourthRoot,embed,hz]⟩
  · have hi : z^2=Complex.I^2 := hn.trans Complex.I_sq.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi with hz | hz
    · exact ⟨1,by simp [fourthRoot,embed,hz]⟩
    · exact ⟨3,by simp [fourthRoot,embed,hz]⟩

theorem word_cases : ∀ x : Fin 4 → Bool,
    evenWord x=true ∨ ∃ j : Fin 4,x=singleWord j ∨ x=complementWord j := by decide

theorem oddTable_even_zero (a b : Fin 4 → ℂ) (x : Fin 4 → Bool) (hx : evenWord x=true) :
    oddTable a b x=0 := by
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [evenWord,h₀,h₁,h₂,h₃] at hx ⊢ <;> simp [oddTable,h₀,h₁,h₂,h₃]

theorem oddTable_reconstruction (f : Signature ℂ 4) (h : ∀ x,evenWord x=true → f x=0) :
    f=oddTable (fun j => f (singleWord j)) (fun j => f (complementWord j)) := by
  funext x
  rcases word_cases x with hx | ⟨j,hx | hx⟩
  · rw [h x hx,oddTable_even_zero _ _ x hx]
  · subst x
    exact (oddTable_single (fun k => f (singleWord k)) (fun k => f (complementWord k)) j).symm
  · subst x
    exact (oddTable_complement (fun k => f (singleWord k)) (fun k => f (complementWord k)) j).symm

theorem normalizedOdd_state (f : Signature ℂ 4) (h : NormalizedOdd f) :
    ∃ s : State,f=complexOdd s := by
  let ac (j : Fin 4) := Classical.choose (fourth_power_code (h.2.2 j).1)
  let bc (j : Fin 4) := Classical.choose (fourth_power_code (h.2.2 j).2)
  have ha (j : Fin 4) : embed (fourthRoot (ac j))=f (singleWord j) :=
    Classical.choose_spec (fourth_power_code (h.2.2 j).1)
  have hb (j : Fin 4) : embed (fourthRoot (bc j))=f (complementWord j) :=
    Classical.choose_spec (fourth_power_code (h.2.2 j).2)
  let s : State := ((ac 1,ac 2,ac 3),(bc 0,bc 1,bc 2,bc 3))
  have hsa (j : Fin 4) : embed (a s j)=f (singleWord j) := by
    fin_cases j
    · simpa [s,a,alpha,fourthRoot,embed] using h.1.symm
    · exact ha 1
    · exact ha 2
    · exact ha 3
  have hsb (j : Fin 4) : embed (b s j)=f (complementWord j) := by
    fin_cases j
    · exact hb 0
    · exact hb 1
    · exact hb 2
    · exact hb 3
  refine ⟨s,(oddTable_reconstruction f h.2.1).trans ?_⟩
  change oddTable _ _=oddTable _ _
  congr 1
  · exact funext (fun j => (hsa j).symm)
  · exact funext (fun j => (hsb j).symm)

end Holant.Certificates.FourthRootOdd
