import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem tetrahedral_translate_0 : ∀b : Fin 7,
    translatedLine .tetrahedral (0 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (0 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (0 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (0 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_1 : ∀b : Fin 7,
    translatedLine .tetrahedral (1 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (1 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (1 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (1 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_2 : ∀b : Fin 7,
    translatedLine .tetrahedral (2 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (2 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (2 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (2 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_3 : ∀b : Fin 7,
    translatedLine .tetrahedral (3 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (3 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (3 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (3 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_4 : ∀b : Fin 7,
    translatedLine .tetrahedral (4 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (4 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (4 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (4 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_5 : ∀b : Fin 7,
    translatedLine .tetrahedral (5 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (5 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (5 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (5 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_6 : ∀b : Fin 7,
    translatedLine .tetrahedral (6 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (6 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (6 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (6 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_7 : ∀b : Fin 7,
    translatedLine .tetrahedral (7 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (7 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (7 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (7 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_8 : ∀b : Fin 7,
    translatedLine .tetrahedral (8 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (8 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (8 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (8 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_9 : ∀b : Fin 7,
    translatedLine .tetrahedral (9 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (9 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (9 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (9 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_10 : ∀b : Fin 7,
    translatedLine .tetrahedral (10 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (10 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (10 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (10 : Fin 12) b)
  decide +kernel

theorem tetrahedral_translate_11 : ∀b : Fin 7,
    translatedLine .tetrahedral (11 : Fin 12) b=globalLine .tetrahedral (translateIndex .tetrahedral (11 : Fin 12) b) := by
  change ∀b : Fin 7, (tetrahedralLines b).image (tetrahedralProductIndex (11 : Fin 12)) =
    tetrahedralSecants (tetrahedralTranslation (11 : Fin 12) b)
  decide +kernel

theorem tetrahedral_witness : ∀t : Fin 34,
    translateIndex .tetrahedral (globalWitness .tetrahedral t).1 (globalWitness .tetrahedral t).2=t := by
  change ∀t : Fin 34, tetrahedralTranslation (tetrahedralWitness t).1 (tetrahedralWitness t).2=t
  decide +kernel

theorem tetrahedral_codes_strictMono : StrictMono (fun t : Fin 34 => lineCode (tetrahedralSecants t)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

theorem tetrahedral_size_distribution :
    (Finset.univ.filter (fun t : Fin 34 => (tetrahedralSecants t).card=2)).card=18 ∧
    (Finset.univ.filter (fun t : Fin 34 => (tetrahedralSecants t).card=3)).card=16 ∧
    (Finset.univ.filter (fun t : Fin 34 => (tetrahedralSecants t).card=4)).card=0 ∧
    (Finset.univ.filter (fun t : Fin 34 => (tetrahedralSecants t).card=5)).card=0 := by decide +kernel

theorem tetrahedral_sizes : ∀t : Fin 34, (tetrahedralSecants t).card=2 ∨ (tetrahedralSecants t).card=3 := by decide +kernel

end Holant.Certificates.PlatonicIncidence
