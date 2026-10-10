import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_translate_0 : ∀b : Fin 31,
    translatedLine .icosahedral (0 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (0 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (0 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (0 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_1 : ∀b : Fin 31,
    translatedLine .icosahedral (1 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (1 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (1 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (1 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_2 : ∀b : Fin 31,
    translatedLine .icosahedral (2 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (2 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (2 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (2 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_3 : ∀b : Fin 31,
    translatedLine .icosahedral (3 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (3 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (3 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (3 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_4 : ∀b : Fin 31,
    translatedLine .icosahedral (4 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (4 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (4 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (4 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_5 : ∀b : Fin 31,
    translatedLine .icosahedral (5 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (5 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (5 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (5 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_6 : ∀b : Fin 31,
    translatedLine .icosahedral (6 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (6 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (6 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (6 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_7 : ∀b : Fin 31,
    translatedLine .icosahedral (7 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (7 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (7 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (7 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_8 : ∀b : Fin 31,
    translatedLine .icosahedral (8 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (8 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (8 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (8 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_9 : ∀b : Fin 31,
    translatedLine .icosahedral (9 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (9 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (9 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (9 : Fin 60) b)
  decide +kernel


end Holant.Certificates.PlatonicIncidence
