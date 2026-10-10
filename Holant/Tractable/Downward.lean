import Holant.Tractable.Criteria

/-!
# Downward inheritance of the seven-alternative criterion

Authoritative `paper1.tex`, rewritten 2026-09-27, Lemma 2.21,
`lem:downward-inheritance`. The public result `downward_inheritance` is the
literal source statement for preprocessed `G ⊆ G'` and the common source-K
image. `Tract.mono_family` proves the stronger statement for arbitrary input
families, including the prescribed zero/nullary preprocessing and empty sets.

The nontrivial branch is proved from the support predicates: a subset of a
single-weight family either retains both strict charge signs, or becomes
one-sided. In the latter case every nonzero central restriction has `n = 2*d`,
equals its original signature, and equals its literal ordered EO completion
with zero added pins. Consequently the original shared sign and A/P class
witness still work; no memberwise replacement of the witness is made.

This establishes inheritance of the structural predicate only. It asserts no
algorithm, FP bound, hardness theorem, or effective recognition procedure.
-/

namespace Holant.Signature

variable {K : Type*} [CommSemiring K] {n d : ℕ}

/-- A nonzero central restriction of one layer forces that layer to be central. -/
theorem SingleLayer.arity_eq_twice_of_centralRestriction_ne_zero
    {f : Signature K n} (h : SingleLayer f d) (hc : centralRestriction f ≠ 0) :
    n = 2 * d := by
  by_contra hn
  apply hc
  funext x
  by_cases hx : 2 * weight x = n
  · have hxd : weight x ≠ d := by omega
    simp [centralRestriction, hx, h x hxd]
  · simp [centralRestriction, hx]

/-- Restriction retains all values of a signature already on the central layer. -/
theorem SingleLayer.centralRestriction_eq_self {f : Signature K n}
    (h : SingleLayer f d) (hn : n = 2 * d) : centralRestriction f = f := by
  funext x
  by_cases hx : 2 * weight x = n
  · simp [centralRestriction, hx]
  · have hxd : weight x ≠ d := by omega
    simp [centralRestriction, hx, h x hxd]

/-- A central layer adds no pins, retains the original port order and scale,
including at arity zero. This is an equality of dependent signatures. -/
theorem completeToEO_eq_self_of_arity_eq_twice (f : Signature K n)
    (hn : n = 2 * d) : completeToEO f d = ⟨n, f⟩ := by
  subst n
  simp only [completeToEO, Nat.le_refl, ite_true, completeWithZeros]
  rw [Nat.sub_self]
  congr 1
  funext x
  simp [tensor_apply]

end Holant.Signature

namespace Holant.Tractable
noncomputable section

/-- Deleting zero and nullary signatures respects family inclusion. -/
theorem preprocess_mono {F G : SignatureFamily AlgebraicComplex} (hGF : G ⊆ F) :
    preprocess G ⊆ preprocess F := fun _ h => ⟨hGF h.1, h.2⟩

/-- A fixed matrix, shared by the family, respects inclusion. -/
theorem familyAction_mono (B : InvertibleKernel)
    {F G : SignatureFamily AlgebraicComplex} (hGF : G ⊆ F) :
    familyAction B G ⊆ familyAction B F := Set.image_mono hGF

theorem kCoordinates_mono {F G : SignatureFamily AlgebraicComplex} (hGF : G ⊆ F) :
    kCoordinates G ⊆ kCoordinates F := familyAction_mono sourceKBasis.symm hGF

theorem centralFamily_mono {F G : SignatureFamily AlgebraicComplex} (hGF : G ⊆ F) :
    centralFamily G ⊆ centralFamily F := by
  rintro h ⟨g, hg, hnz, heq⟩
  exact ⟨g, hGF hg, hnz, heq⟩

theorem completionFamily_mono {F G : SignatureFamily AlgebraicComplex} (hGF : G ⊆ F) :
    completionFamily G ⊆ completionFamily F := by
  rintro h ⟨g, hg, hnz, d, hd, heq⟩
  exact ⟨g, hGF hg, hnz, d, hd, heq⟩

/-- The finite-subset operation preserves the same outer sign and class witnesses. -/
theorem EOTract.mono_family {F G : SignatureFamily AlgebraicComplex}
    (h : EOTract F) (hGF : G ⊆ F) : EOTract G := by
  rcases h with ⟨hfin, heo, sign, C, hxor, hpair⟩
  exact ⟨hfin.subset hGF, fun g hg => heo g (hGF hg), sign, C,
    fun g hg => hxor g (hGF hg), fun g hg => hpair g (hGF hg)⟩

/-- On a family of single layers, every retained central restriction is literally
one of its ordered completions, not merely equivalent up to a scalar or ports. -/
theorem centralFamily_subset_completionFamily
    {G : SignatureFamily AlgebraicComplex}
    (hlayers : ∀ g ∈ G, ∃ d, Signature.SingleLayer g.2 d) :
    centralFamily G ⊆ completionFamily G := by
  rintro h ⟨g, hg, hcentral, rfl⟩
  obtain ⟨d, hd⟩ := hlayers g hg
  have hn := hd.arity_eq_twice_of_centralRestriction_ne_zero hcentral
  have hself := hd.centralRestriction_eq_self hn
  have hnonzero : g.2 ≠ 0 := by simpa only [hself] using hcentral
  refine ⟨g, hg, hnonzero, d, hd, ?_⟩
  rw [hself, Signature.completeToEO_eq_self_of_arity_eq_twice g.2 hn]

theorem CommonOneSided.mono_family {F G : SignatureFamily AlgebraicComplex}
    (h : CommonOneSided F) (hGF : G ⊆ F) : CommonOneSided G := by
  rcases h with h | h
  · exact Or.inl (fun g hg => h g (hGF hg))
  · exact Or.inr (fun g hg => h g (hGF hg))

/-- A family that lacks either strict sign has a common weak support side.
No nonemptiness or nonzero-membership assumptions are required. -/
theorem commonOneSided_or_bothChargeSigns (G : SignatureFamily AlgebraicComplex) :
    CommonOneSided G ∨ BothChargeSigns G := by
  classical
  by_cases hn : ∃ g ∈ G, ∃ x, g.2 x ≠ 0 ∧ Holant.charge x < 0
  · by_cases hp : ∃ g ∈ G, ∃ x, g.2 x ≠ 0 ∧ 0 < Holant.charge x
    · exact Or.inr ⟨hn, hp⟩
    · left
      right
      intro g hg x hx
      by_contra hc
      exact hp ⟨g, hg, x, hx, lt_of_not_ge hc⟩
  · left
    left
    intro g hg x hx
    by_contra hc
    exact hn ⟨g, hg, x, hx, lt_of_not_ge hc⟩

theorem OneSidedAlternative.mono_family {F G : SignatureFamily AlgebraicComplex}
    (h : OneSidedAlternative F) (hGF : G ⊆ F) : OneSidedAlternative G :=
  ⟨h.1.mono_family (kCoordinates_mono hGF),
    h.2.mono_family (centralFamily_mono (kCoordinates_mono hGF))⟩

/-- Unlike the other alternatives, single-weight inheritance may change clauses:
losing a strict charge sign switches to the one-sided alternative. -/
theorem SingleWeightAlternative.mono_family
    {F G : SignatureFamily AlgebraicComplex}
    (h : SingleWeightAlternative F) (hGF : G ⊆ F) :
    OneSidedAlternative G ∨ SingleWeightAlternative G := by
  have hK := kCoordinates_mono hGF
  have hlayers : ∀ g ∈ kCoordinates G, ∃ d, Signature.SingleLayer g.2 d :=
    fun g hg => h.1 g (hK hg)
  have hcompletion : EOTract (completionFamily (kCoordinates G)) :=
    h.2.2.mono_family (completionFamily_mono hK)
  rcases commonOneSided_or_bothChargeSigns (kCoordinates G) with hside | hboth
  · exact Or.inl ⟨hside,
      hcompletion.mono_family (centralFamily_subset_completionFamily hlayers)⟩
  · exact Or.inr ⟨hlayers, hboth, hcompletion⟩

theorem ArityTwoAlternative.mono_family {F G : SignatureFamily AlgebraicComplex}
    (h : ArityTwoAlternative F) (hGF : G ⊆ F) : ArityTwoAlternative G :=
  fun g hg => h g (hGF hg)

theorem MatchingAlternative.mono_family {F G : SignatureFamily AlgebraicComplex}
    (h : MatchingAlternative F) (hGF : G ⊆ F) : MatchingAlternative G := by
  rcases h with h | h
  · exact Or.inl (fun g hg => h g (hGF hg))
  · exact Or.inr (fun g hg => h g (hGF hg))

/-- All seven actual structural alternatives are inherited by subfamilies. -/
theorem TractCore.mono_family {F G : SignatureFamily AlgebraicComplex}
    (h : TractCore F) (hGF : G ⊆ F) : TractCore G := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (h.mono_family hGF)
  · rcases h.mono_family hGF with hside | hsingle
    · exact Or.inl hside
    · exact Or.inr (Or.inl hsingle)
  · exact Or.inr (Or.inr (Or.inl (h.mono_family hGF)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h.mono_family hGF))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.mono_family hGF)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.mono_family hGF))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.mono_family hGF))))))

/-- Full criterion inheritance, including preprocessing, finiteness and empty sets. -/
theorem Tract.mono_family {F G : SignatureFamily AlgebraicComplex}
    (h : Tract F) (hGF : G ⊆ F) : Tract G :=
  ⟨h.1.subset (preprocess_mono hGF), h.2.mono_family (preprocess_mono hGF)⟩

/-- Lemma 2.21 (`lem:downward-inheritance`) in the source's K-transported form.
Both signature sets satisfy the source preprocessing convention. The stronger
public theorem above shows that these two domain hypotheses are not needed. -/
theorem downward_inheritance {G G' : SignatureFamily AlgebraicComplex}
    (_hG : Preprocessed G) (_hG' : Preprocessed G') (hGG' : G ⊆ G')
    (h : Tract (familyAction sourceKBasis G')) : Tract (familyAction sourceKBasis G) :=
  h.mono_family (familyAction_mono sourceKBasis hGG')

end
end Holant.Tractable
