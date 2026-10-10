import Holant.ReedMuller.TwoChart.Fibers

/-! Genuine original support vectors witnessing different self-dual chart
directions, and exact survival at each original chart shift. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 theorem selfDual_eq_of_le (D E : BinaryCode n) (hD : SelfDual D) (hE : SelfDual E)
    (h : D≤E) : D=E := by
  apply le_antisymm h
  intro x hx
  apply (hD x).mpr
  intro y hy
  exact (hE x).mp hx y (h hy)

 theorem different_direction_witness (C₀ C₁ : Chart n) (hne : C₀.direction≠C₁.direction) :
    ∃ s t : BinaryVector n,s∈C₀.direction ∧ s∉C₁.direction ∧ t∈C₁.direction ∧
      dot s t=1 ∧ dot s s=0 ∧ dot t t=0 := by
  have hnot : ¬C₀.direction≤C₁.direction := fun h =>
    hne (selfDual_eq_of_le _ _ C₀.selfDual C₁.selfDual h)
  have hs : ∃ s,s∈C₀.direction ∧ s∉C₁.direction := by
    by_contra h
    apply hnot
    intro x hx
    by_contra hnx
    exact h ⟨x,hx,hnx⟩
  obtain ⟨s,hs,hsn⟩ := hs
  have ht : ∃ t,t∈C₁.direction ∧ dot s t≠0 := by
    by_contra h
    apply hsn
    apply (C₁.selfDual s).mpr
    intro t ht
    by_contra hnt
    exact h ⟨t,ht,hnt⟩
  obtain ⟨t,ht,hst⟩ := ht
  refine ⟨s,t,hs,hsn,ht,(binary_cases _).resolve_left hst,?_,?_⟩
  · exact (C₀.selfDual s).mp hs s hs
  · exact (C₁.selfDual t).mp ht t ht

 theorem chartFiber_shift_eq (C : Chart n) (J : BinaryCode n) :
    chartFiber C J C.shift=Finset.univ.filter (fun j : J => j.val∈C.direction) := by
  ext j
  simp [chartFiber,add_sub_cancel_left]

 theorem signedChartSum_shift_nonzero (C : Chart n) (J : BinaryCode n) (chi : Character n)
    (hchi : ∀ j : J,chi j.val=C.character j.val) :
    signedChartSum C J chi C.shift≠0 := by
  apply (signedChartSum_nonzero_iff C J chi hchi _).mpr
  exact ⟨0,by simp⟩

 theorem chartFiber_same_direction (C₀ C₁ : Chart n) (hD : C₀.direction=C₁.direction)
    (J : BinaryCode n) : chartFiber C₀ J C₀.shift=chartFiber C₁ J C₁.shift := by
  rw [chartFiber_shift_eq,chartFiber_shift_eq,hD]

 theorem signedChartSum_shift_ratio_fourth (C₀ C₁ : Chart n) (hD : C₀.direction=C₁.direction)
    (J : BinaryCode n) (chi : Character n)
    (h₀ : ∀ j : J,chi j.val=C₀.character j.val)
    (h₁ : ∀ j : J,chi j.val=C₁.character j.val) :
    (signedChartSum C₁ J chi C₁.shift/signedChartSum C₀ J chi C₀.shift)^4=
      (C₁.scalar/C₀.scalar)^4 := by
  have hc : ((chartFiber C₀ J C₀.shift).card : AlgebraicComplex)≠0 := by
    have hn := signedChartSum_shift_nonzero C₀ J chi h₀
    rw [signedChartSum_eq_card C₀ J chi h₀] at hn
    exact (mul_ne_zero_iff.mp hn).1
  rw [signedChartSum_eq_card C₀ J chi h₀,signedChartSum_eq_card C₁ J chi h₁,
    ←chartFiber_same_direction C₀ C₁ hD J]
  simp only [div_pow,mul_pow,fourthRootPhase_pow_four,mul_one]
  field_simp [hc,C₀.nonzero]

end
end Holant.ReedMuller.TwoChart
