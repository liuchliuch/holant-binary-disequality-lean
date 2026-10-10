import Holant.ReedMuller.TwoChart.FlatLocalization
import Holant.ReedMuller.TwoChart.NativeXExpansionContext

/-! Source Lemma 7.17, `lem:rm-two-chart-localization`.

Source clause map:
* `RadonFrame` records the accessible direction and orthogonal quotient frame;
  `actual_flat_radon_chart_obstruction` extracts both nonzero constant charts
  from the two actual zero-or-flat plus cards and nonaffinity of `orbitPlus`.
* `exists_localizingData` constructs the retained nonalternating space and its
  self-dual complementary relation, with even output arity at most eight.
* `LocalizingData.context_flat` makes that relation genuinely phase-free.
* `LocalizingData.output_nonaffine_different` retains the missing parallelogram;
  `LocalizingData.output_ratio_fourth` retains the forbidden fourth-root ratio.
* `LocalizingData.output_orbitPlus` and `original_output_nonaffine` transfer
  this obstruction to the contraction with the original algebraic input g.
* `one_copy_flat_IRM_context_realization` realizes that contraction, with its
  nonzero scalar, by one original g vertex, literal I/RM vertices, and native
  X edges. Its literal-X expansion preserves loops, parallel edges, nullary
  factors and ordered output ports by exact ordinary-network denotation.
* `source_flat_two_chart_localization` derives the final quadratic bounds.
  The physical-network and Gadget consumers below remove recorded graph/Bell
  scalars and coordinate isometries by proved identities, never by assuming
  transformed or reindexed signatures are available as resources.
-/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Complete source 7.17: only the original g, literal I and literal RM are
signature resources. Disequality occurs as the actual native edge tensor. -/
theorem source_flat_two_chart_localization {n : ℕ} (hn10 : 10≤n) (hnEven : Even n)
    (F : RadonAccess.RadonFrame n) (g : Signature AlgebraicComplex n)
    (hcards : ∀ d,FlatOrZero (fun x =>
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x)))
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (N : Network AlgebraicComplex m),m≤8 ∧
      OneInputOccurrence algebraicIRMFamily g N ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote≠0 ∧ ¬Affine N.denote ∧
      N.shape.vertices≤40*n^2+10*n+2 ∧ N.shape.edges≤52*n^2+10*n+1 := by
  obtain ⟨C₀,C₁,hchar₀,hchar₁,h₀,h₁,ho⟩ := actual_flat_radon_chart_obstruction F g hcards hna
  obtain ⟨L⟩ := exists_localizingData F hnEven C₀ C₁
  have houtput := L.original_output_nonaffine g h₀ h₁ ho
  obtain ⟨k,hk⟩ := hnEven.add L.size_even
  have hnm : n+L.outputSize=2*k := by omega
  have hkn : k≤n := by have hm:=L.size_le;omega
  have hk2 : k^2≤n^2 := Nat.pow_le_pow_left hkn 2
  obtain ⟨N,s,hs,hN,hE,hD,hV,hEdges⟩ :=
    one_copy_flat_IRM_context_realization k hnm hn10 g L.context (L.context_flat hchar₀)
  have hdenote : N.denote=fun y => s*L.output g y := by
    funext y
    rw [hD,L.context_contraction]
  have hnaN : ¬Affine N.denote := by
    rw [hdenote]
    exact nonaffine_nonzero_scale _ houtput s hs
  refine ⟨L.outputSize,N,L.size_le,hN,hE,nonaffine_nonzero _ hnaN,hnaN,?_,?_⟩
  · omega
  · omega

/-- At source arity at least ten, even label equality identifies exactly one
original g occurrence, since the other physical vertices have arity two/eight. -/
theorem OneInputOccurrence.unique_IRM_input {n m : ℕ} (hn10 : 10≤n)
    {g : Signature AlgebraicComplex n} {N : Network AlgebraicComplex m}
    (hN : OneInputOccurrence algebraicIRMFamily g N) :
    ∃! v : Fin N.shape.vertices,
      (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex)=⟨n,g⟩ := by
  obtain ⟨v,hv,hrest⟩ := hN
  refine ⟨v,hv,?_⟩
  intro w hw
  by_contra hne
  have hr := hrest w hne
  rcases hr with hi|hrm
  · have hn := congrArg Sigma.fst (hw.symm.trans hi)
    simp only at hn
    omega
  · have hn := congrArg Sigma.fst (hw.symm.trans hrm)
    simp only at hn
    omega

/-- Actual fixed orthogonal-graph/Bell plus-card networks imply the source
hypothesis after removing their recorded nonzero scalars and affine isometry.
Their Bell representatives are used only to test cards, not as output resources. -/
theorem source_flat_two_chart_from_actual_networks {n : ℕ}
    (hn10 : 10≤n+2) (hnEven : Even (n+2))
    (κ : ZMod 2→ZMod 2→ℂ) (hκ : ∀d l,κ d l≠0)
    (F : RadonAccess.RadonFrame (n+2)) (G : SignedRadon.ActualGraph κ F.A)
    (g : Signature AlgebraicComplex (n+2))
    (hcards : ∀d,FlatOrZero (SignedRadon.signedNetwork F G (fun x => (g x:ℂ)) d 0).denote)
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (N : Network AlgebraicComplex m),m≤8 ∧
      OneInputOccurrence algebraicIRMFamily g N ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote≠0 ∧ ¬Affine N.denote ∧
      N.shape.vertices≤40*(n+2)^2+10*(n+2)+2 ∧
      N.shape.edges≤52*(n+2)^2+10*(n+2)+1 := by
  apply source_flat_two_chart_localization hn10 hnEven F g _ hna
  intro d
  exact RadonFrame.flat_native_network_implies_actualRadon hκ F G
    (fun x => (g x:ℂ)) d (hcards d)

/-- Direct Gadget consumer with precisely the original g and literal I/RM. -/
theorem source_flat_two_chart_gadget {n : ℕ} (hn10 : 10≤n) (hnEven : Even n)
    (F : RadonAccess.RadonFrame n) (g : Signature AlgebraicComplex n)
    (hcards : ∀d,FlatOrZero (fun x =>
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x)))
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (H : Signature AlgebraicComplex m),m≤8 ∧ H≠0 ∧ ¬Affine H ∧
      Gadget.Realizes (insert (⟨n,g⟩ : AnySignature AlgebraicComplex) algebraicIRMFamily)
        .disequality H := by
  obtain ⟨m,N,hm,hN,hE,hz,ha,hV,he⟩ :=
    source_flat_two_chart_localization hn10 hnEven F g hcards hna
  exact ⟨m,N.denote,hm,hz,ha,hN.realizes hE⟩

/-- Fully physical input-to-Gadget API; no normalized card or freely supplied
change of basis appears among its hypotheses or resource signatures. -/
theorem source_flat_two_chart_gadget_from_actual_networks {n : ℕ}
    (hn10 : 10≤n+2) (hnEven : Even (n+2))
    (κ : ZMod 2→ZMod 2→ℂ) (hκ : ∀d l,κ d l≠0)
    (F : RadonAccess.RadonFrame (n+2)) (G : SignedRadon.ActualGraph κ F.A)
    (g : Signature AlgebraicComplex (n+2))
    (hcards : ∀d,FlatOrZero (SignedRadon.signedNetwork F G (fun x => (g x:ℂ)) d 0).denote)
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (H : Signature AlgebraicComplex m),m≤8 ∧ H≠0 ∧ ¬Affine H ∧
      Gadget.Realizes (insert (⟨n+2,g⟩ : AnySignature AlgebraicComplex) algebraicIRMFamily)
        .disequality H := by
  obtain ⟨m,N,hm,hN,hE,hz,ha,hV,he⟩ :=
    source_flat_two_chart_from_actual_networks hn10 hnEven κ hκ F G g hcards hna
  exact ⟨m,N.denote,hm,hz,ha,hN.realizes hE⟩

end
end Holant.ReedMuller.TwoChart
