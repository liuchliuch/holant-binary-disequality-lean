import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFiberDichotomy
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineMatchingVariation

/-! Four live tomographic terms in a safe tensor vary on precisely two
original matching edges. This transfers the physical overlap theorem to the
literal fiber labels rather than assuming any support condition. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators
namespace Fiber
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

def LabelVaries (labels : Label → Fin r → Label) (e : Fin r) : Prop :=
  ∃ a b, labels a e ≠ labels b e

theorem coefficient_scale (M : Matching P r) (q : Tensor ℂ P) (c : ℂ) (labels : Fin r → Label) :
    M.coefficient (fun x => c*q x) labels = c*M.coefficient q labels := by
  simp only [Matching.coefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem safe_four_variable_edges (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished : Fin r)
    (hlabel : ∀ a, labels a distinguished = a) (hw : ∀ a, weight a ≠ 0)
    (hs : MatchingCard.PauliMatchingOrZero (tensor M weight labels)) :
    ∃ i j : Fin r, i ≠ j ∧ ∀ e, LabelVaries labels e → e = i ∨ e = j := by
  classical
  rcases hs with hz | ⟨s,N,fixed,c,hc,he⟩
  · exact False.elim (hw 0 ((zero_iff M weight labels distinguished hlabel).mp hz 0))
  have hr : s = r := by
    have hM := M.port_card
    have hN := N.port_card
    omega
  subst s
  have hlive : Fintype.card {a : Label // weight a ≠ 0} = 4 := by
    have hh := Fintype.card_congr (Equiv.subtypeUnivEquiv hw)
    exact hh.trans card_label
  have hcount := support_card M weight labels distinguished hlabel
  rw [hlive,he,M.scaled_overlap_support_card N fixed c hc] at hcount
  have ho : Fintype.card {a : Fin r → Label // M.overlap N fixed a ≠ 0} = 4 := by
    rw [M.overlap_support_card N]
    exact hcount
  obtain ⟨i,j,hij,hvar⟩ := M.support_four_exactly_two_varying_edges N fixed ho
  refine ⟨i,j,hij,?_⟩
  intro e hve
  apply (hvar e).mp
  obtain ⟨a,b,hab⟩ := hve
  have hnonzero (a : Label) : M.overlap N fixed (labels a) ≠ 0 := by
    have hh := coefficient_at M weight labels distinguished hlabel a
    rw [he,coefficient_scale] at hh
    intro hz
    change M.coefficient (N.tensor fixed) (labels a) = 0 at hz
    rw [hz,mul_zero] at hh
    exact hw a hh.symm
  exact ⟨labels a,labels b,hnonzero a,hnonzero b,hab⟩

theorem three_variable_edges_not_safe (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished : Fin r)
    (hlabel : ∀ a, labels a distinguished = a) (hw : ∀ a, weight a ≠ 0)
    (e f g : Fin r) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : LabelVaries labels e) (hf : LabelVaries labels f) (hg : LabelVaries labels g) :
    ¬ MatchingCard.PauliMatchingOrZero (tensor M weight labels) := by
  intro hs
  obtain ⟨i,j,hij,hvar⟩ := safe_four_variable_edges M weight labels distinguished hlabel hw hs
  rcases hvar e he with h | h <;> rcases hvar f hf with h' | h' <;>
    rcases hvar g hg with h'' | h'' <;> simp_all

end Fiber
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
