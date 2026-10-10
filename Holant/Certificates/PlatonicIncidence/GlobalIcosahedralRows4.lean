import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_translate_40 : ∀b : Fin 31,
    translatedLine .icosahedral (40 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (40 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (40 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (40 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_41 : ∀b : Fin 31,
    translatedLine .icosahedral (41 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (41 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (41 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (41 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_42 : ∀b : Fin 31,
    translatedLine .icosahedral (42 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (42 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (42 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (42 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_43 : ∀b : Fin 31,
    translatedLine .icosahedral (43 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (43 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (43 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (43 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_44 : ∀b : Fin 31,
    translatedLine .icosahedral (44 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (44 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (44 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (44 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_45 : ∀b : Fin 31,
    translatedLine .icosahedral (45 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (45 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (45 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (45 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_46 : ∀b : Fin 31,
    translatedLine .icosahedral (46 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (46 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (46 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (46 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_47 : ∀b : Fin 31,
    translatedLine .icosahedral (47 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (47 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (47 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (47 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_48 : ∀b : Fin 31,
    translatedLine .icosahedral (48 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (48 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (48 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (48 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_49 : ∀b : Fin 31,
    translatedLine .icosahedral (49 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (49 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (49 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (49 : Fin 60) b)
  decide +kernel


end Holant.Certificates.PlatonicIncidence
