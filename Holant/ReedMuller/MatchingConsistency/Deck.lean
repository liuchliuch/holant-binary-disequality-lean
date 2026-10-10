import Holant.ReedMuller.MatchingConsistency.Pairing

/-! The exact physical proper-card semantics gives named-port equality
matchings. All representative scalars are canceled only after their proved
nonvanishing; the tensor and its residual port order stay explicit. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.FixedCoreDeck
open Holant.ReedMuller.CoefficientAtlas Holant.Certificates.MatchingContractionClosure
variable {ι κ K : Type*}

 def Pairing.reindex (M : Pairing ι) (e : ι ≃ κ) : Pairing κ where
  mate x := e (M.mate (e.symm x))
  involutive x := by
    dsimp
    rw [Equiv.symm_apply_apply,M.involutive,Equiv.apply_symm_apply]
  ne_self x := by
    intro h
    have hh := e.injective (h.trans (e.apply_symm_apply x).symm)
    exact M.ne_self _ hh

 theorem EqualityMatchingOrZero.reindex [Zero K] {q : Tensor K ι}
    (h : EqualityMatchingOrZero q) (e : ι ≃ κ) :
    EqualityMatchingOrZero (Tensor.reindex e q) := by
  rcases h with rfl | ⟨M,hM⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨M.reindex e,?_⟩
    intro x
    rw [Tensor.reindex,hM]
    constructor
    · intro h i
      simpa [Pairing.reindex] using h (e.symm i)
    · intro h i
      simpa [Pairing.reindex] using h (e i)

 theorem EqualityMatchingOrZero.of_smul [Field K] {q : Tensor K ι} (c : K) (hc : c≠0)
    (h : EqualityMatchingOrZero (c • q)) : EqualityMatchingOrZero q := by
  rcases h with hz | ⟨M,hM⟩
  · left
    funext x
    exact (mul_eq_zero.mp (congrFun hz x)).resolve_left hc
  · right
    refine ⟨M,?_⟩
    intro x
    constructor
    · intro hx
      exact (hM x).mp (mul_ne_zero hc hx)
    · intro hx
      exact (mul_ne_zero_iff.mp ((hM x).mpr hx)).2

 def EqualityDeck [DecidableEq ι] [Field K] (f : Tensor K ι) : Prop :=
  ∀i j : ι,i≠j → ∀ minus : Bool, EqualityMatchingOrZero (card f i j minus)

 theorem actual_equality_deck {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (hdeck : ActualMatchingDeck G R f) : EqualityDeck (walsh f) := by
  intro i j hij minus
  have hm : EqualityMatchingOrZero (walsh (representativeCard R f
      (Holant.Dihedral.CompatibleClosure.pairOrder i j) minus)) := by
    rcases walsh_matchingOrZero hG hspan (hdeck _ minus) with h | ⟨r,M,hM⟩
    · exact Or.inl h
    · rw [←hM]
      exact weighted_equalityMatching M
  rw [representativeCard_exact,walsh_smul,walsh_physical_card] at hm
  have h := EqualityMatchingOrZero.of_smul (R.scale minus) (R.scale_ne_zero minus) hm
  rw [card_named_ordered _ i j hij minus]
  exact h.reindex (residualOrder i j hij)

 theorem EqualityDeck.nonzeroAtZero [DecidableEq ι] [Field K] {f : Tensor K ι}
    (h : EqualityDeck f) : NonzeroAtZeroCards f := by
  intro i j hij minus hn
  exact ((h i j hij minus).zero_value).resolve_left hn

/-- A chosen optional matching, still tied to the tensor's literal support. -/
structure SelectedMatching [Zero K] (q : Tensor K ι) where
  pairing : Option (Pairing ι)
  exact : ∀x,q x≠0 ↔ ∃ M,pairing=some M ∧ M.Support x

 def EqualityMatchingOrZero.select [Zero K] {q : Tensor K ι}
    (h : EqualityMatchingOrZero q) : SelectedMatching q := by
  classical
  by_cases hz : q=0
  · exact ⟨none,by simp [hz]⟩
  · let M := Classical.choose (h.resolve_left hz)
    have hM := Classical.choose_spec (h.resolve_left hz)
    exact ⟨some M,by intro x; simpa only [Option.some.injEq,exists_eq_left'] using hM x⟩

end Holant.ReedMuller.MatchingConsistency
