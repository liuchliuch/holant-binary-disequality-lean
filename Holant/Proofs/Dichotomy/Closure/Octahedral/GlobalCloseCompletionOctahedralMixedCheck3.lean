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

theorem reconstruction_1_8 :
    rawReconstructed true (TetrahedralDeck.words 8) = prototype true (TetrahedralDeck.words 8) := by
  decide +kernel

theorem mixed_1_8 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 8) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 8) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_9 :
    rawReconstructed true (TetrahedralDeck.words 9) = prototype true (TetrahedralDeck.words 9) := by
  decide +kernel

theorem mixed_1_9 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 9) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 9) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_10 :
    rawReconstructed true (TetrahedralDeck.words 10) = prototype true (TetrahedralDeck.words 10) := by
  decide +kernel

theorem mixed_1_10 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 10) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 10) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_11 :
    rawReconstructed true (TetrahedralDeck.words 11) = prototype true (TetrahedralDeck.words 11) := by
  decide +kernel

theorem mixed_1_11 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 11) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 11) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_12 :
    rawReconstructed true (TetrahedralDeck.words 12) = prototype true (TetrahedralDeck.words 12) := by
  decide +kernel

theorem mixed_1_12 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 12) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 12) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_13 :
    rawReconstructed true (TetrahedralDeck.words 13) = prototype true (TetrahedralDeck.words 13) := by
  decide +kernel

theorem mixed_1_13 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 13) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 13) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_14 :
    rawReconstructed true (TetrahedralDeck.words 14) = prototype true (TetrahedralDeck.words 14) := by
  decide +kernel

theorem mixed_1_14 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 14) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 14) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

theorem reconstruction_1_15 :
    rawReconstructed true (TetrahedralDeck.words 15) = prototype true (TetrahedralDeck.words 15) := by
  decide +kernel

theorem mixed_1_15 :
    Signature.coordinateAction (mixedPorts true) (prototype true) (TetrahedralDeck.words 15) =
      exteriorScale true * mixedShape true imag (TetrahedralDeck.words 15) := by
  rw [mixedPorts_exact]
  simp only [cachedMixedPorts,diagonal_fourth_action]
  decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.MixedEndpointBridge
