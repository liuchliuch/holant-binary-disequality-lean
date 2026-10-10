import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_translate_10 : ∀b : Fin 31,
    translatedLine .icosahedral (10 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (10 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (10 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (10 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_11 : ∀b : Fin 31,
    translatedLine .icosahedral (11 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (11 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (11 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (11 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_12 : ∀b : Fin 31,
    translatedLine .icosahedral (12 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (12 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (12 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (12 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_13 : ∀b : Fin 31,
    translatedLine .icosahedral (13 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (13 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (13 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (13 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_14 : ∀b : Fin 31,
    translatedLine .icosahedral (14 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (14 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (14 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (14 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_15 : ∀b : Fin 31,
    translatedLine .icosahedral (15 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (15 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (15 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (15 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_16 : ∀b : Fin 31,
    translatedLine .icosahedral (16 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (16 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (16 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (16 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_17 : ∀b : Fin 31,
    translatedLine .icosahedral (17 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (17 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (17 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (17 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_18 : ∀b : Fin 31,
    translatedLine .icosahedral (18 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (18 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (18 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (18 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_19 : ∀b : Fin 31,
    translatedLine .icosahedral (19 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (19 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (19 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (19 : Fin 60) b)
  decide +kernel


end Holant.Certificates.PlatonicIncidence
