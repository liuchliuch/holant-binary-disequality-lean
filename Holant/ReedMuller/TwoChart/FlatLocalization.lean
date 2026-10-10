import Holant.ReedMuller.TwoChart.Localization
import Holant.ReedMuller.TwoChart.FlatCharts
import Holant.ReedMuller.TwoChart.ContextKernelFlat
import Holant.ReedMuller.TwoChart.ContextRealizationFlat

/-! Conditional pure-flat localization with literal I/X/RM signature vertices.
The final source7.17 boundary still requires eliminating literal-X signature
occurrences when only native-X links and literal I are supplied. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem flat_two_chart_with_literal_ix_vertices {n : ℕ} (hn10 : 10≤n) (hnEven : Even n)
    (F : RadonAccess.RadonFrame n) (g : Signature AlgebraicComplex n)
    (hcards : ∀ d,FlatOrZero (fun x =>
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x)))
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (N : Network AlgebraicComplex m),m≤8 ∧
      OneInputOccurrence algebraicNativeFamily g N ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote≠0 ∧ ¬Affine N.denote ∧
      N.shape.vertices≤20*n^2+5*n+1 ∧ N.shape.edges≤32*n^2+5*n := by
  obtain ⟨C₀,C₁,hchar₀,hchar₁,h₀,h₁,ho⟩ := actual_flat_radon_chart_obstruction F g hcards hna
  obtain ⟨L⟩ := exists_localizingData F hnEven C₀ C₁
  have houtput := L.original_output_nonaffine g h₀ h₁ ho
  obtain ⟨k,hk⟩ := hnEven.add L.size_even
  have hnm : n+L.outputSize=2*k := by omega
  have hkn : k≤n := by have hm:=L.size_le;omega
  have hk2 : k^2≤n^2 := Nat.pow_le_pow_left hkn 2
  obtain ⟨N,s,hs,hN,hE,hD,hV,hEdges⟩ := one_copy_flat_context_realization k hnm g L.context
    (L.context_flat hchar₀)
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
