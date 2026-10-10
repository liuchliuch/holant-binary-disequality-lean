import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_translate_50 : ∀b : Fin 31,
    translatedLine .icosahedral (50 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (50 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (50 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (50 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_51 : ∀b : Fin 31,
    translatedLine .icosahedral (51 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (51 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (51 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (51 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_52 : ∀b : Fin 31,
    translatedLine .icosahedral (52 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (52 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (52 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (52 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_53 : ∀b : Fin 31,
    translatedLine .icosahedral (53 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (53 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (53 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (53 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_54 : ∀b : Fin 31,
    translatedLine .icosahedral (54 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (54 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (54 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (54 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_55 : ∀b : Fin 31,
    translatedLine .icosahedral (55 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (55 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (55 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (55 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_56 : ∀b : Fin 31,
    translatedLine .icosahedral (56 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (56 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (56 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (56 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_57 : ∀b : Fin 31,
    translatedLine .icosahedral (57 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (57 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (57 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (57 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_58 : ∀b : Fin 31,
    translatedLine .icosahedral (58 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (58 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (58 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (58 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_59 : ∀b : Fin 31,
    translatedLine .icosahedral (59 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (59 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (59 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (59 : Fin 60) b)
  decide +kernel


end Holant.Certificates.PlatonicIncidence
