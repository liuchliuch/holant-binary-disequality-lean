import Holant.ReedMuller.TwoChart.BoundaryObstruction
import Holant.ReedMuller.TwoChart.ContextKernelSum
import Holant.ReedMuller.TwoChart.ContextRealization

/-! Complete character-aware two-chart localization with a literal one-input
algebraic network and original fixed RM/Bell resources. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {F : RadonAccess.RadonFrame n} {C₀ C₁ : Chart (n-2)}

 theorem LocalizingData.original_output_nonaffine (L : LocalizingData F C₀ C₁)
    (g : Signature AlgebraicComplex n)
    (h₀ : algebraicRadon F 0 g=C₀.eval) (h₁ : algebraicRadon F 1 g=C₁.eval)
    (ho : C₀.direction≠C₁.direction ∨ (C₁.scalar/C₀.scalar)^4≠1) : ¬Affine (L.output g) := by
  have hna := L.output_nonaffine ho
  have he : L.output (orbitPlus F.v g)=L.output (twoChartSum F C₀ C₁) := by
    rw [orbitPlus_eq_lifted_charts F g C₀ C₁ h₀ h₁]
    rfl
  rw [←he,L.output_orbitPlus g] at hna
  intro h
  exact hna (h.two_translate (wordVector L.outputTranslation))

 theorem nonaffine_nonzero {m : ℕ} (f : Signature AlgebraicComplex m) (hf : ¬Affine f) : f≠0 := by
  intro hz
  apply hf
  rw [hz]
  exact affine_zero m

 theorem nonaffine_nonzero_scale {m : ℕ} (f : Signature AlgebraicComplex m)
    (hf : ¬Affine f) (c : AlgebraicComplex) (hc : c≠0) :
    ¬Affine (fun x => c*f x) := by
  intro h
  apply hf
  have H := h.scale c⁻¹
  convert H using 1
  funext x
  simp only [←mul_assoc,inv_mul_cancel₀ hc,one_mul]

/-- Source7.23. Charts may vanish; the input is arbitrary algebraic g and is
not assumed affine. The output network has exactly one distinguished original
g occurrence and no additional signature outside the fixed actual resources. -/
theorem source_character_two_chart_localization {n : ℕ} (hn10 : 10≤n) (hnEven : Even n)
    (κ : ZMod 2→ZMod 2→AlgebraicComplex) (hκ : ∀d l,κ d l≠0)
    (F : RadonAccess.RadonFrame n) (g : Signature AlgebraicComplex n)
    (hcards : ∀ d,CFlat (fun x =>
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x)))
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (N : Network AlgebraicComplex m),m≤8 ∧
      OneInputOccurrence (algebraicRetainedFamily κ) g N ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote≠0 ∧ ¬Affine N.denote ∧
      N.shape.vertices≤20*n^2+7*n+1 ∧ N.shape.edges≤32*n^2+7*n := by
  obtain ⟨C₀,C₁,h₀,h₁,ho⟩ := actual_radon_chart_obstruction F g hcards hna
  obtain ⟨L⟩ := exists_localizingData F hnEven C₀ C₁
  have houtput := L.original_output_nonaffine g h₀ h₁ ho
  obtain ⟨k,hk⟩ := hnEven.add L.size_even
  have hnm : n+L.outputSize=2*k := by omega
  have hkn : k≤n := by have hm:=L.size_le;omega
  have hk2 : k^2≤n^2 := Nat.pow_le_pow_left hkn 2
  obtain ⟨N,s,hs,hN,hE,hD,hV,hEdges⟩ := one_copy_context_realization κ hκ k hnm g L.context
    (Or.inr L.context_nonzeroFlat) L.context_ne_zero
  have hdenote : N.denote=fun y => s*L.output g y := by
    funext y
    rw [hD,L.context_contraction]
  have hnaN : ¬Affine N.denote := by
    rw [hdenote]
    exact nonaffine_nonzero_scale _ houtput s hs
  refine ⟨L.outputSize,N,L.size_le,hN,hE,nonaffine_nonzero _ hnaN,hnaN,?_,?_⟩
  · omega
  · omega

end
end Holant.ReedMuller.TwoChart
