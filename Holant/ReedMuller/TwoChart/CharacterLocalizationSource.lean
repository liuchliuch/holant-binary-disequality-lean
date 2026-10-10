import Holant.ReedMuller.TwoChart.Localization
import Holant.ReedMuller.CharacterRecognition.SignedPhysical

/-! Direct source7.23 consumer of the actual fixed orthogonal graph and Bell
plus-card networks. Every normalization is removed by a proved nonzero scalar
and affine-isometry identity. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem source_character_two_chart_from_actual_networks {n : ℕ}
    (hn10 : 10≤n+2) (hnEven : Even (n+2))
    (κ : ZMod 2→ZMod 2→AlgebraicComplex) (hκ : ∀d l,κ d l≠0)
    (F : RadonAccess.RadonFrame (n+2))
    (G : SignedRadon.ActualGraph (fun d l => (κ d l:ℂ)) F.A)
    (g : Signature AlgebraicComplex (n+2))
    (hcards : ∀ d,CFlat (SignedRadon.signedNetwork F G (fun x => (g x:ℂ)) d 0).denote)
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (N : Network AlgebraicComplex m),m≤8 ∧
      OneInputOccurrence (algebraicRetainedFamily κ) g N ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote≠0 ∧ ¬Affine N.denote ∧
      N.shape.vertices≤20*(n+2)^2+7*(n+2)+1 ∧ N.shape.edges≤32*(n+2)^2+7*(n+2) := by
  apply source_character_two_chart_localization hn10 hnEven κ hκ F g _ hna
  intro d
  have hκ' : ∀d l,(κ d l:ℂ)≠0 := by
    intro d l
    exact_mod_cast hκ d l
  have H := CharacterRecognition.SignedTransport.cflat_native_network_implies_actualSignedRadon
    hκ' F G (fun x => (g x:ℂ)) d 0 (hcards d)
  simpa only [CharacterRecognition.SignedTransport.actualSignedRadon_plus] using H

 theorem source_character_two_chart_gadget {n : ℕ} (hn10 : 10≤n) (hnEven : Even n)
    (κ : ZMod 2→ZMod 2→AlgebraicComplex) (hκ : ∀d l,κ d l≠0)
    (F : RadonAccess.RadonFrame n) (g : Signature AlgebraicComplex n)
    (hcards : ∀ d,CFlat (fun x =>
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x)))
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ (m : ℕ) (H : Signature AlgebraicComplex m),m≤8 ∧ H≠0 ∧ ¬Affine H ∧
      Gadget.Realizes (insert (⟨n,g⟩ : AnySignature AlgebraicComplex) (algebraicRetainedFamily κ))
        .disequality H := by
  obtain ⟨m,N,hm,hN,hE,hz,ha,hV,he⟩ :=
    source_character_two_chart_localization hn10 hnEven κ hκ F g hcards hna
  exact ⟨m,N.denote,hm,hz,ha,hN.realizes hE⟩

end
end Holant.ReedMuller.TwoChart
