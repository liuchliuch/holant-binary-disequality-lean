import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineRulingPairPorts

/-! A shared original-port ruling gives one actual common product basis.
The change of orientation/enumeration is proved through faithful overlap
coordinates; no equality of ordered factor lists is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators

namespace Matching
variable {P : Type*} [Fintype P] [LinearOrder P] {r s : ℕ}

theorem common_ruling_exponent (M N : Matching P r) (h : M.mate = N.mate) :
    r-M.cycleCount N = 0 := by
  rw [←M.sum_cycle_extras N]
  apply Finset.sum_eq_zero
  intro c hc
  have he := (M.cycleLength_one_iff_common N c).mpr (congrArg (fun m : Equiv.Perm P => m c.val) h)
  simp only [he,Nat.sub_self]

theorem representation_of_same_ruling (M : Matching P r) (N : Matching P s)
    (h : M.mate = N.mate) (labels : Fin s → Label) (c : ℂ) (hc : c ≠ 0) :
    ∃ fixed : Fin r → Label, ∃ d : ℂ, d ≠ 0 ∧
      (fun x => c*N.tensor labels x) = (fun x => d*M.tensor fixed x) := by
  classical
  have hr : s = r := by
    have hM := M.port_card
    have hN := N.port_card
    omega
  subst s
  let q : Tensor ℂ P := fun x => c*N.tensor labels x
  have hcount := M.scaled_overlap_support_card N labels c hc
  rw [M.common_ruling_exponent N h,pow_zero] at hcount
  obtain ⟨b,hb⟩ := Fintype.card_eq_one_iff.mp hcount
  refine ⟨b.val,M.coefficient q b.val,b.property,?_⟩
  funext x
  have he := M.expansion q x
  rw [Finset.sum_eq_single b.val] at he
  · exact he.symm
  · intro a ha hab
    have hz : M.coefficient q a = 0 := by
      by_contra hn
      exact hab (congrArg Subtype.val (hb ⟨a,hn⟩))
    rw [hz,zero_mul]
  · simp

end Matching

namespace MatchingCard

/-- Each original dual card is represented in ONE fixed physical matching.
Weights are zero exactly on the zero cards, with no normalization or removal
of nonzero complex scales. -/
theorem common_card_coordinates (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : f ≠ 0) (hs : OrderedPairSafe f) :
    ∃ s : ℕ, ∃ M : Matching (Fin (2*r+4)) s,
      ∃ weight : Label → ℂ, ∃ labels : Label → Fin s → Label,
        (∀ a, Signature.contract (dual a) f = fun x => weight a*M.tensor (labels a) x) ∧
        (∀ a, weight a = 0 ↔ Signature.contract (dual a) f = 0) := by
  classical
  obtain ⟨s,M,hM⟩ := fixed_ruling r hr f hf hs (Equiv.refl _)
  have hrep (a : Label) : ∃ w : ℂ, ∃ labels : Fin s → Label,
      Signature.contract (dual a) f = (fun x => w*M.tensor labels x) ∧
      (w = 0 ↔ Signature.contract (dual a) f = 0) := by
    have hcard : PauliMatchingOrZero (Signature.contract (dual a) f) := hs (Equiv.refl _) a
    rcases hcard with hz | ⟨t,N,labels,c,hc,hN⟩
    · refine ⟨0,fun _ => 0,?_,?_⟩
      · rw [hz]; funext x; exact (zero_mul _).symm
      · simp only [hz,iff_self]
    · have hmate := hM a t N labels c hc hN
      obtain ⟨fixed,d,hd,he⟩ := M.representation_of_same_ruling N hmate.symm labels c hc
      refine ⟨d,fixed,hN.trans he,?_⟩
      have hn : Signature.contract (dual a) f ≠ 0 := by
        rw [hN]
        exact scaled_matching_ne_zero N labels c hc
      simp only [hd,hn,iff_self]
  choose weight labels he hz using hrep
  exact ⟨s,M,weight,labels,he,hz⟩

end MatchingCard
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
