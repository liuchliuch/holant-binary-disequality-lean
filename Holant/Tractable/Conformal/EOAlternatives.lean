import Holant.Tractable.Conformal.Shape

/-! Transport of the two full EO alternatives, including ordered completion. -/
namespace Holant.Tractable
noncomputable section
namespace Conformal

theorem shape_centralFamily_related {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t) (hs : s ≠ 0) (ht : t ≠ 0)
    (G : SignatureFamily AlgebraicComplex) :
    ∀ h ∈ centralFamily (familyAction D G), ∃ g ∈ centralFamily G, Related opposite g h := by
  rintro h ⟨dg, ⟨g, hg, rfl⟩, hnz, rfl⟩
  have he := shape_centralRestriction hD g.2
  have hgnz : Signature.centralRestriction g.2 ≠ 0 := by
    intro hz
    apply hnz
    rw [he, hz]
    funext x
    simp
  refine ⟨⟨g.1, Signature.centralRestriction g.2⟩,
    ⟨g, hg, hgnz, rfl⟩, s ^ (g.1 - g.1 / 2) * t ^ (g.1 / 2),
    mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ ht), ?_⟩
  exact congrArg (fun f => (⟨g.1, f⟩ : AnySignature AlgebraicComplex)) he

theorem shape_completionFamily_related {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t) (hs : s ≠ 0) (ht : t ≠ 0)
    {G : SignatureFamily AlgebraicComplex}
    (hlayers : ∀ g ∈ G, ∃ d, Signature.SingleLayer g.2 d) :
    ∀ h ∈ completionFamily (familyAction D G),
      ∃ g ∈ completionFamily G, Related opposite g h := by
  rintro h ⟨dg, ⟨g, hg, rfl⟩, hnz, e, he, rfl⟩
  obtain ⟨d, hd⟩ := hlayers g hg
  have hgnz : g.2 ≠ 0 := fun hz => hnz ((action_eq_zero_iff D g.2).mpr hz)
  have hle := singleLayer_le_arity hgnz hd
  have hlayer := shape_singleLayer hD hd hle
  have heq : e = flipLayer opposite g.1 d := Signature.singleLayer_unique hnz he hlayer
  let c := s ^ (g.1 - flipLayer opposite g.1 d) * t ^ flipLayer opposite g.1 d
  refine ⟨Signature.completeToEO g.2 d, ⟨g, hg, hgnz, d, hd, rfl⟩,
    c, mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ ht), ?_⟩
  change Signature.completeToEO (D.action g.2) e = mapSignature opposite c _
  rw [heq, shape_action_singleLayer hD hd hle, completeToEO_scale_flip g.2 hle]

theorem shape_all_singleLayer {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t)
    {G : SignatureFamily AlgebraicComplex}
    (hlayers : ∀ g ∈ G, ∃ d, Signature.SingleLayer g.2 d) :
    ∀ g ∈ familyAction D G, ∃ d, Signature.SingleLayer g.2 d := by
  rintro h ⟨g, hg, rfl⟩
  by_cases hz : g.2 = 0
  · refine ⟨0, ?_⟩
    change Signature.SingleLayer (D.action g.2) 0
    rw [(action_eq_zero_iff D g.2).mpr hz]
    exact fun _ _ => rfl
  · obtain ⟨d, hd⟩ := hlayers g hg
    exact ⟨flipLayer opposite g.1 d, shape_singleLayer hD hd (singleLayer_le_arity hz hd)⟩

/-- Clause (1) preserves its family-wide support side, or exchanges the two sides,
while its EO witness has the corresponding one shared sign and A/P class. -/
theorem oneSided_map {D : InvertibleKernel} (hD : XConformal D)
    {G : SignatureFamily AlgebraicComplex} (hfin : G.Finite)
    (hG : OneSidedAlternative (familyAction sourceKBasis G)) :
    OneSidedAlternative (familyAction sourceKBasis (familyAction D G)) := by
  have hG' : CommonOneSided G ∧ EOTract (centralFamily G) := by
    simpa only [OneSidedAlternative, kCoordinates_familyAction] using hG
  obtain ⟨opposite, s, t, hs, ht, hshape⟩ := hasShape_of_xConformal hD
  change CommonOneSided (kCoordinates _) ∧ EOTract (centralFamily (kCoordinates _))
  simp only [kCoordinates_familyAction]
  refine ⟨shape_commonOneSided hshape hs ht hG'.1, ?_⟩
  exact eoTract_transport hG'.2 (centralFamily_finite (hfin.image _)) opposite
    (shape_centralFamily_related hshape hs ht G)

/-- Clause (2) retains both strict charge signs, every single-layer condition,
and the exact ordered completion, with all zero completions deleted as defined. -/
theorem singleWeight_map {D : InvertibleKernel} (hD : XConformal D)
    {G : SignatureFamily AlgebraicComplex} (hfin : G.Finite)
    (hG : SingleWeightAlternative (familyAction sourceKBasis G)) :
    SingleWeightAlternative (familyAction sourceKBasis (familyAction D G)) := by
  have hG' : (∀ g ∈ G, ∃ d, Signature.SingleLayer g.2 d) ∧
      BothChargeSigns G ∧ EOTract (completionFamily G) := by
    simpa only [SingleWeightAlternative, kCoordinates_familyAction] using hG
  obtain ⟨opposite, s, t, hs, ht, hshape⟩ := hasShape_of_xConformal hD
  unfold SingleWeightAlternative
  simp only [kCoordinates_familyAction]
  refine ⟨shape_all_singleLayer hshape hG'.1,
    shape_bothChargeSigns hshape hs ht hG'.2.1, ?_⟩
  exact eoTract_transport hG'.2.2 (completionFamily_finite (hfin.image _)) opposite
    (shape_completionFamily_related hshape hs ht hG'.1)

end Conformal
end
end Holant.Tractable
