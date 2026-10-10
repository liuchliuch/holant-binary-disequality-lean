import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineAlternatingOrbits

/-! A disagreement-preserving contraction pair for two physical matchings.
The chosen pair lies in distinct edges of BOTH matchings. This avoids all
possibly vanishing same-edge traces during the reduction to four ports. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
namespace Matching
variable {P : Type*} {r s : ℕ} [Fintype P] [DecidableEq P]

/-- Mate of a surviving port after cross-splicing the two selected endpoints.
The actual surgery-to-this-formula correspondence is a separate interface. -/
def spliceMateValue (M : Matching P r) (u v w : P) : P :=
  if M.mate w = u then M.mate v else if M.mate w = v then M.mate u else M.mate w

private theorem exists_avoiding_four (p a b c : P) (hc : 4 < Fintype.card P) :
    ∃ q : P, q ≠ p ∧ q ≠ a ∧ q ≠ b ∧ q ≠ c := by
  classical
  have hcard : ({p,a,b,c} : Finset P).card ≤ 4 := by
    have h₁ := Finset.card_insert_le p ({a,b,c} : Finset P)
    have h₂ := Finset.card_insert_le a ({b,c} : Finset P)
    have h₃ := Finset.card_insert_le b ({c} : Finset P)
    have h₄ : ({c} : Finset P).card = 1 := Finset.card_singleton c
    omega
  by_contra hn
  have hsub : (Finset.univ : Finset P) ⊆ {p,a,b,c} := by
    intro q hq
    by_contra hmem
    have hneq : q ≠ p ∧ q ≠ a ∧ q ≠ b ∧ q ≠ c := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hmem
    exact hn ⟨q,hneq⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_univ] at hh
  omega

/-- Starting from any marked disagreement, delete that marked port and one
other original port while retaining an explicit surviving disagreement. -/
theorem disagreement_preserving_pair (M : Matching P r) (N : Matching P s) (p : P)
    (hp : M.mate p ≠ N.mate p) (hcard : 4 < Fintype.card P) :
    ∃ v w : P, p ≠ v ∧ M.mate p ≠ v ∧ N.mate p ≠ v ∧
      w ≠ p ∧ w ≠ v ∧ M.spliceMateValue p v w ≠ N.spliceMateValue p v w := by
  let a := M.mate p
  let b := N.mate p
  let c := N.mate a
  have ha : a ≠ p := M.mate_ne_self p
  have hca : c ≠ a := N.mate_ne_self a
  have hcp : c ≠ p := by
    intro h
    have hh := congrArg N.mate h
    change N.mate (N.mate a) = N.mate p at hh
    rw [N.mate_mate] at hh
    exact hp hh
  have hcb : c ≠ b := by
    intro h
    change N.mate a = N.mate p at h
    exact ha (N.mate.injective h)
  have hMa : M.mate a = p := M.mate_mate p
  have hNa : N.mate a = c := rfl
  by_cases hclose : M.mate c = b
  · obtain ⟨q,hqp,hqa,hqb,hqc⟩ := exists_avoiding_four p a b c hcard
    have hMc : M.mate q ≠ c := by
      intro h
      have hh := congrArg M.mate h
      rw [M.mate_mate,hclose] at hh
      exact hqb hh
    refine ⟨q,a,hqp.symm,hqa.symm,hqb.symm,ha,hqa.symm,?_⟩
    simpa only [spliceMateValue,hMa,hNa,ite_true,hcp,ite_false,Ne.symm hqc] using hMc
  · refine ⟨c,a,hcp.symm,hca.symm,hcb.symm,ha,hca.symm,?_⟩
    simpa only [spliceMateValue,hMa,hNa,ite_true,hcp,ite_false] using hclose

/-- More than four residual ports can always be reduced by a pair which is
cross-edge in both distinct rulings and retains a witnessed disagreement. -/
theorem distinct_rulings_have_reduction_pair (M : Matching P r) (N : Matching P s)
    (hne : M.mate ≠ N.mate) (hcard : 4 < Fintype.card P) :
    ∃ u v w : P, u ≠ v ∧ M.mate u ≠ v ∧ N.mate u ≠ v ∧
      w ≠ u ∧ w ≠ v ∧ M.spliceMateValue u v w ≠ N.spliceMateValue u v w := by
  obtain ⟨p,hp⟩ : ∃ p : P, M.mate p ≠ N.mate p := by
    by_contra hn
    push_neg at hn
    exact hne (Equiv.ext hn)
  obtain ⟨v,w,h⟩ := M.disagreement_preserving_pair N p hp hcard
  exact ⟨p,v,w,h⟩

end Matching
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
