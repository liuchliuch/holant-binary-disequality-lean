import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem octahedral_translate_0 : ∀b : Fin 13,
    translatedLine .octahedral (0 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (0 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (0 : Fin 24)) =
    octahedralSecants (octahedralTranslation (0 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_1 : ∀b : Fin 13,
    translatedLine .octahedral (1 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (1 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (1 : Fin 24)) =
    octahedralSecants (octahedralTranslation (1 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_2 : ∀b : Fin 13,
    translatedLine .octahedral (2 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (2 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (2 : Fin 24)) =
    octahedralSecants (octahedralTranslation (2 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_3 : ∀b : Fin 13,
    translatedLine .octahedral (3 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (3 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (3 : Fin 24)) =
    octahedralSecants (octahedralTranslation (3 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_4 : ∀b : Fin 13,
    translatedLine .octahedral (4 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (4 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (4 : Fin 24)) =
    octahedralSecants (octahedralTranslation (4 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_5 : ∀b : Fin 13,
    translatedLine .octahedral (5 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (5 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (5 : Fin 24)) =
    octahedralSecants (octahedralTranslation (5 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_6 : ∀b : Fin 13,
    translatedLine .octahedral (6 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (6 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (6 : Fin 24)) =
    octahedralSecants (octahedralTranslation (6 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_7 : ∀b : Fin 13,
    translatedLine .octahedral (7 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (7 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (7 : Fin 24)) =
    octahedralSecants (octahedralTranslation (7 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_8 : ∀b : Fin 13,
    translatedLine .octahedral (8 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (8 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (8 : Fin 24)) =
    octahedralSecants (octahedralTranslation (8 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_9 : ∀b : Fin 13,
    translatedLine .octahedral (9 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (9 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (9 : Fin 24)) =
    octahedralSecants (octahedralTranslation (9 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_10 : ∀b : Fin 13,
    translatedLine .octahedral (10 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (10 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (10 : Fin 24)) =
    octahedralSecants (octahedralTranslation (10 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_11 : ∀b : Fin 13,
    translatedLine .octahedral (11 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (11 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (11 : Fin 24)) =
    octahedralSecants (octahedralTranslation (11 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_12 : ∀b : Fin 13,
    translatedLine .octahedral (12 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (12 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (12 : Fin 24)) =
    octahedralSecants (octahedralTranslation (12 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_13 : ∀b : Fin 13,
    translatedLine .octahedral (13 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (13 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (13 : Fin 24)) =
    octahedralSecants (octahedralTranslation (13 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_14 : ∀b : Fin 13,
    translatedLine .octahedral (14 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (14 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (14 : Fin 24)) =
    octahedralSecants (octahedralTranslation (14 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_15 : ∀b : Fin 13,
    translatedLine .octahedral (15 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (15 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (15 : Fin 24)) =
    octahedralSecants (octahedralTranslation (15 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_16 : ∀b : Fin 13,
    translatedLine .octahedral (16 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (16 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (16 : Fin 24)) =
    octahedralSecants (octahedralTranslation (16 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_17 : ∀b : Fin 13,
    translatedLine .octahedral (17 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (17 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (17 : Fin 24)) =
    octahedralSecants (octahedralTranslation (17 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_18 : ∀b : Fin 13,
    translatedLine .octahedral (18 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (18 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (18 : Fin 24)) =
    octahedralSecants (octahedralTranslation (18 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_19 : ∀b : Fin 13,
    translatedLine .octahedral (19 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (19 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (19 : Fin 24)) =
    octahedralSecants (octahedralTranslation (19 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_20 : ∀b : Fin 13,
    translatedLine .octahedral (20 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (20 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (20 : Fin 24)) =
    octahedralSecants (octahedralTranslation (20 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_21 : ∀b : Fin 13,
    translatedLine .octahedral (21 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (21 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (21 : Fin 24)) =
    octahedralSecants (octahedralTranslation (21 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_22 : ∀b : Fin 13,
    translatedLine .octahedral (22 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (22 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (22 : Fin 24)) =
    octahedralSecants (octahedralTranslation (22 : Fin 24) b)
  decide +kernel

theorem octahedral_translate_23 : ∀b : Fin 13,
    translatedLine .octahedral (23 : Fin 24) b=globalLine .octahedral (translateIndex .octahedral (23 : Fin 24) b) := by
  change ∀b : Fin 13, (octahedralLines b).image (octahedralProductIndex (23 : Fin 24)) =
    octahedralSecants (octahedralTranslation (23 : Fin 24) b)
  decide +kernel

theorem octahedral_witness : ∀t : Fin 122,
    translateIndex .octahedral (globalWitness .octahedral t).1 (globalWitness .octahedral t).2=t := by
  change ∀t : Fin 122, octahedralTranslation (octahedralWitness t).1 (octahedralWitness t).2=t
  decide +kernel

theorem octahedral_codes_strictMono : StrictMono (fun t : Fin 122 => lineCode (octahedralSecants t)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

theorem octahedral_size_distribution :
    (Finset.univ.filter (fun t : Fin 122 => (octahedralSecants t).card=2)).card=72 ∧
    (Finset.univ.filter (fun t : Fin 122 => (octahedralSecants t).card=3)).card=32 ∧
    (Finset.univ.filter (fun t : Fin 122 => (octahedralSecants t).card=4)).card=18 ∧
    (Finset.univ.filter (fun t : Fin 122 => (octahedralSecants t).card=5)).card=0 := by decide +kernel

theorem octahedral_sizes : ∀t : Fin 122, (octahedralSecants t).card=2 ∨ (octahedralSecants t).card=3 ∨ (octahedralSecants t).card=4 := by decide +kernel

end Holant.Certificates.PlatonicIncidence
