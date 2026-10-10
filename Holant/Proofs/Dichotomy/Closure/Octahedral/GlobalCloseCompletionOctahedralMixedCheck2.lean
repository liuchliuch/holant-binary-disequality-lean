import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMixedData

set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.MixedEndpointBridge
open Holant Holant.Algebraic Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.MainChain
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.QuotientEnumeration RankTwo.HarmonicProjectivities
open RankTwo.PhysicalOrbit RankTwo.CanonicalEndpointBridge
open scoped Matrix BigOperators

theorem reconstruction_1_0 :
    rawReconstructed true (TetrahedralDeck.words 0) = prototype true (TetrahedralDeck.words 0) := by
  decide +kernel

theorem mixed_1_0 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 0) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 0) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_1 :
    rawReconstructed true (TetrahedralDeck.words 1) = prototype true (TetrahedralDeck.words 1) := by
  decide +kernel

theorem mixed_1_1 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 1) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 1) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_2 :
    rawReconstructed true (TetrahedralDeck.words 2) = prototype true (TetrahedralDeck.words 2) := by
  decide +kernel

theorem mixed_1_2 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 2) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 2) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_3 :
    rawReconstructed true (TetrahedralDeck.words 3) = prototype true (TetrahedralDeck.words 3) := by
  decide +kernel

theorem mixed_1_3 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 3) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 3) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_4 :
    rawReconstructed true (TetrahedralDeck.words 4) = prototype true (TetrahedralDeck.words 4) := by
  decide +kernel

theorem mixed_1_4 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 4) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 4) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_5 :
    rawReconstructed true (TetrahedralDeck.words 5) = prototype true (TetrahedralDeck.words 5) := by
  decide +kernel

theorem mixed_1_5 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 5) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 5) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_6 :
    rawReconstructed true (TetrahedralDeck.words 6) = prototype true (TetrahedralDeck.words 6) := by
  decide +kernel

theorem mixed_1_6 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 6) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 6) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_7 :
    rawReconstructed true (TetrahedralDeck.words 7) = prototype true (TetrahedralDeck.words 7) := by
  decide +kernel

theorem mixed_1_7 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 7) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 7) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.MixedEndpointBridge
