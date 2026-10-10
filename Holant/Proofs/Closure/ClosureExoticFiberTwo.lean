import Holant.Proofs.Closure.ClosureExoticFiberFull
import Holant.Proofs.Closure.ClosureExoticOverlapTwo

/-! A genuinely safe proper output with four distinct live fibre rows can vary
on only two matching edges. Applications must supply that actual output's safety. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Holant Holant.Pauli.ExoticKlein
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

theorem safe_four_rows_only_two (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished : Fin r)
    (hlabel : ∀ a,labels a distinguished=a) (hlive : ∀ a,weight a≠0)
    (safe : MatchingCard.ExoticMatchingOrZero (Fiber.tensor M weight labels)) :
    ∃ e f : Fin r,e≠f ∧ ∀ a b : Label,∀ j,j≠e → j≠f → labels a j=labels b j := by
  classical
  rcases safe with hz | ⟨t,N,fixed,c,hc,he⟩
  · have hw := (Fiber.zero_iff M weight labels distinguished hlabel).mp hz
    exact False.elim (hlive 0 (hw 0))
  have htr : t=r := by have hm:=M.port_card;have hn:=N.port_card;omega
  subst t
  have hcoef (b : Fin r → Label) :
      M.coefficient (Fiber.tensor M weight labels) b=c*M.overlap N fixed b := by
    rw [he]
    simp only [Matching.coefficient,Matching.overlap,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hcount : Fintype.card {b : Fin r → Label // M.overlap N fixed b≠0}=4 := by
    calc
      _=Fintype.card {b : Fin r → Label // M.coefficient (Fiber.tensor M weight labels) b≠0} := by
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro b
        rw [hcoef]
        exact ⟨fun h => mul_ne_zero hc h,fun h => (mul_ne_zero_iff.mp h).2⟩
      _=Fintype.card {a : Label // weight a≠0} := Fiber.support_card M weight labels distinguished hlabel
      _=4 := by simp only [hlive,ne_eq,not_false_eq_true,Fintype.card_subtype_true,card_label]
  have hrow (a : Label) : M.overlap N fixed (labels a)≠0 := by
    have h := hlive a
    rw [←Fiber.coefficient_at M weight labels distinguished hlabel a,hcoef] at h
    exact (mul_ne_zero_iff.mp h).2
  obtain ⟨e,f,hef,houtside⟩ := ClosureExoticOverlapTwo.overlap_four_only_two M N fixed hcount
  exact ⟨e,f,hef,fun a b j hje hjf => houtside (labels a) (labels b) (hrow a) (hrow b) j hje hjf⟩

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
