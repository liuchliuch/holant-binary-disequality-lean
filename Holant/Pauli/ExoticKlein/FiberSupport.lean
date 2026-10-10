import Holant.Pauli.ExoticKlein.MatchingGroup
import Holant.Pauli.ExoticKlein.MatchingSupport

/-! Exact support of a tomographic fiber, with zero weights retained. The
original distinguished edge label prevents cancellation between summands. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
namespace Fiber
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]

 def tensor (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label) : Tensor ℂ P :=
  fun x => ∑ a, weight a*M.tensor (labels a) x

 theorem coefficient (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a) (b : Fin r → Label) :
    M.coefficient (tensor M weight labels) b =
      if b = labels (b distinguished) then weight (b distinguished) else 0 := by
  classical
  unfold Matching.coefficient tensor
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ x, M.dualTensor b x*(weight a*M.tensor (labels a) x)) =
        ∑ a, weight a*M.coefficient (M.tensor (labels a)) b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Matching.coefficient,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ a, if b = labels a then weight a else 0 := by
      simp only [Matching.same_matching_coefficient,mul_ite,mul_one,mul_zero]
    _ = _ := by
      apply Finset.sum_eq_single (b distinguished)
      · intro a ha hne
        have hn : b ≠ labels a := by
          intro he
          have hh := congrFun he distinguished
          rw [hlabel] at hh
          exact hne hh.symm
        simp only [hn,ite_false]
      · simp

 theorem coefficient_at (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a) (a : Label) :
    M.coefficient (tensor M weight labels) (labels a) = weight a := by
  rw [coefficient M weight labels distinguished hlabel,hlabel]
  simp only [ite_true]

 def supportEquiv (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a) :
    {a : Label // weight a ≠ 0} ≃
      {b : Fin r → Label // M.coefficient (tensor M weight labels) b ≠ 0} where
  toFun a := ⟨labels a.val,by rw [coefficient_at M weight labels distinguished hlabel]; exact a.property⟩
  invFun b := ⟨b.val distinguished,by
    have hh := b.property
    rw [coefficient M weight labels distinguished hlabel] at hh
    split_ifs at hh with he
    · exact hh
    · exact False.elim (hh rfl)⟩
  left_inv a := Subtype.ext (hlabel a.val)
  right_inv b := by
    apply Subtype.ext
    have hh := b.property
    rw [coefficient M weight labels distinguished hlabel] at hh
    split_ifs at hh with he
    · exact he.symm
    · exact False.elim (hh rfl)

 theorem support_card (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a) :
    Fintype.card {b : Fin r → Label // M.coefficient (tensor M weight labels) b ≠ 0} =
      Fintype.card {a : Label // weight a ≠ 0} :=
  (Fintype.card_congr (supportEquiv M weight labels distinguished hlabel)).symm

 theorem zero_iff (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a) :
    tensor M weight labels = 0 ↔ ∀ a, weight a = 0 := by
  constructor
  · intro hz a
    have he := coefficient_at M weight labels distinguished hlabel a
    rw [hz] at he
    simp only [Matching.coefficient,Pi.zero_apply,mul_zero,Finset.sum_const_zero] at he
    exact he.symm
  · intro hz
    funext x
    simp only [tensor,hz,zero_mul,Finset.sum_const_zero,Pi.zero_apply]

/-- A safe actual fiber has zero, one or four live coefficients. This follows
from the proved physical matching-overlap support theorem, with no sampled
scales or assumed coefficient-vanishing condition. -/
 theorem safe_support_card (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a)
    (hs : MatchingCard.ExoticMatchingOrZero (tensor M weight labels)) :
    Fintype.card {a : Label // weight a ≠ 0} = 0 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 1 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 4 := by
  classical
  rcases hs with hz | ⟨s,N,fixed,c,hc,he⟩
  · left
    have hw := (zero_iff M weight labels distinguished hlabel).mp hz
    simp only [hw,ne_eq,not_true_eq_false]
    exact Fintype.card_eq_zero
  · have hr : s = r := by
      have hM := M.port_card
      have hN := N.port_card
      omega
    subst s
    have hcount := M.scaled_overlap_support_card N fixed c hc
    rw [←he,support_card M weight labels distinguished hlabel] at hcount
    have hbound : Fintype.card {a : Label // weight a ≠ 0} ≤ 4 := by
      simpa only [card_label] using Fintype.card_subtype_le (fun a : Label => weight a ≠ 0)
    right
    cases hx : r-M.cycleCount N with
    | zero => left; simpa only [hx,pow_zero] using hcount
    | succ n =>
      cases n with
      | zero => right; simpa only [hx,Nat.zero_add,pow_one] using hcount
      | succ n =>
        have hp : 0 < (4 : ℕ)^n := pow_pos (by decide) n
        rw [hcount,hx,pow_succ,pow_succ] at hbound
        nlinarith

end Fiber
end
end Holant.Pauli.ExoticKlein
