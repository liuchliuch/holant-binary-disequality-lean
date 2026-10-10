import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_translate_20 : ∀b : Fin 31,
    translatedLine .icosahedral (20 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (20 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (20 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (20 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_21 : ∀b : Fin 31,
    translatedLine .icosahedral (21 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (21 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (21 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (21 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_22 : ∀b : Fin 31,
    translatedLine .icosahedral (22 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (22 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (22 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (22 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_23 : ∀b : Fin 31,
    translatedLine .icosahedral (23 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (23 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (23 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (23 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_24 : ∀b : Fin 31,
    translatedLine .icosahedral (24 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (24 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (24 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (24 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_25 : ∀b : Fin 31,
    translatedLine .icosahedral (25 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (25 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (25 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (25 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_26 : ∀b : Fin 31,
    translatedLine .icosahedral (26 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (26 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (26 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (26 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_27 : ∀b : Fin 31,
    translatedLine .icosahedral (27 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (27 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (27 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (27 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_28 : ∀b : Fin 31,
    translatedLine .icosahedral (28 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (28 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (28 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (28 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_29 : ∀b : Fin 31,
    translatedLine .icosahedral (29 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (29 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (29 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (29 : Fin 60) b)
  decide +kernel


end Holant.Certificates.PlatonicIncidence
