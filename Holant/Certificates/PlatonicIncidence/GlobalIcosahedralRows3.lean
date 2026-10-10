import Holant.Certificates.PlatonicIncidence.GlobalData
import Holant.Certificates.PlatonicIncidence.Secants

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_translate_30 : ∀b : Fin 31,
    translatedLine .icosahedral (30 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (30 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (30 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (30 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_31 : ∀b : Fin 31,
    translatedLine .icosahedral (31 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (31 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (31 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (31 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_32 : ∀b : Fin 31,
    translatedLine .icosahedral (32 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (32 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (32 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (32 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_33 : ∀b : Fin 31,
    translatedLine .icosahedral (33 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (33 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (33 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (33 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_34 : ∀b : Fin 31,
    translatedLine .icosahedral (34 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (34 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (34 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (34 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_35 : ∀b : Fin 31,
    translatedLine .icosahedral (35 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (35 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (35 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (35 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_36 : ∀b : Fin 31,
    translatedLine .icosahedral (36 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (36 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (36 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (36 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_37 : ∀b : Fin 31,
    translatedLine .icosahedral (37 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (37 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (37 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (37 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_38 : ∀b : Fin 31,
    translatedLine .icosahedral (38 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (38 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (38 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (38 : Fin 60) b)
  decide +kernel

theorem icosahedral_translate_39 : ∀b : Fin 31,
    translatedLine .icosahedral (39 : Fin 60) b=globalLine .icosahedral (translateIndex .icosahedral (39 : Fin 60) b) := by
  change ∀b : Fin 31, (icosahedralLines b).image (icosahedralProductIndex (39 : Fin 60)) =
    icosahedralSecants (icosahedralTranslation (39 : Fin 60) b)
  decide +kernel


end Holant.Certificates.PlatonicIncidence
