import Holant.Certificates.PlatonicIncidence.IcosahedralCardChecks
import Holant.Certificates.PlatonicIncidence.GlobalIcosahedralRows0
import Holant.Certificates.PlatonicIncidence.GlobalIcosahedralRows1
import Holant.Certificates.PlatonicIncidence.GlobalIcosahedralRows2
import Holant.Certificates.PlatonicIncidence.GlobalIcosahedralRows3
import Holant.Certificates.PlatonicIncidence.GlobalIcosahedralRows4
import Holant.Certificates.PlatonicIncidence.GlobalIcosahedralRows5
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit0
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit1
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit2
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit3
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit4
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit5
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit6
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit7
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit8
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit9
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit10
import Holant.Certificates.PlatonicIncidence.IcosahedralAudit11

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_entry (t : Fin 722) : IcosahedralEntry t := by
  by_cases h0 : t.val<64
  · exact icosahedral_entries_0 t (by omega) h0
  by_cases h1 : t.val<128
  · exact icosahedral_entries_1 t (by omega) h1
  by_cases h2 : t.val<192
  · exact icosahedral_entries_2 t (by omega) h2
  by_cases h3 : t.val<256
  · exact icosahedral_entries_3 t (by omega) h3
  by_cases h4 : t.val<320
  · exact icosahedral_entries_4 t (by omega) h4
  by_cases h5 : t.val<384
  · exact icosahedral_entries_5 t (by omega) h5
  by_cases h6 : t.val<448
  · exact icosahedral_entries_6 t (by omega) h6
  by_cases h7 : t.val<512
  · exact icosahedral_entries_7 t (by omega) h7
  by_cases h8 : t.val<576
  · exact icosahedral_entries_8 t (by omega) h8
  by_cases h9 : t.val<640
  · exact icosahedral_entries_9 t (by omega) h9
  by_cases h10 : t.val<704
  · exact icosahedral_entries_10 t (by omega) h10
  exact icosahedral_entries_11 t (by omega) t.isLt

theorem icosahedral_witness : ∀t : Fin 722,
    translateIndex .icosahedral (globalWitness .icosahedral t).1 (globalWitness .icosahedral t).2=t :=
  fun t => (icosahedral_entry t).1

theorem icosahedral_codes_strictMono : StrictMono (fun t : Fin 722 => lineCode (icosahedralSecants t)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro t
  have h := (icosahedral_entry t.castSucc).2.2
  dsimp only [Fin.val_castSucc] at h
  rw [dif_pos (show t.val+1<722 by omega)] at h
  exact h

theorem icosahedral_card (t : Fin 722) : (icosahedralSecants t).card=icosahedralCard t :=
  (icosahedral_entry t).2.1

theorem icosahedral_size_distribution :
    (Finset.univ.filter (fun t : Fin 722 => (icosahedralSecants t).card=2)).card=450 ∧
    (Finset.univ.filter (fun t : Fin 722 => (icosahedralSecants t).card=3)).card=200 ∧
    (Finset.univ.filter (fun t : Fin 722 => (icosahedralSecants t).card=4)).card=0 ∧
    (Finset.univ.filter (fun t : Fin 722 => (icosahedralSecants t).card=5)).card=72 := by
  have h :
      (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=2)).card=450 ∧
      (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=3)).card=200 ∧
      (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=4)).card=0 ∧
      (Finset.univ.filter (fun t : Fin 722 => icosahedralCard t=5)).card=72 := icosahedral_vector_size_distribution
  simpa only [icosahedral_card] using h

theorem icosahedral_card_options : ∀t : Fin 722,icosahedralCard t=2 ∨ icosahedralCard t=3 ∨ icosahedralCard t=5 := by
  exact icosahedral_vector_card_options

theorem icosahedral_sizes : ∀t : Fin 722, (icosahedralSecants t).card=2 ∨ (icosahedralSecants t).card=3 ∨ (icosahedralSecants t).card=5 := by
  intro t
  simpa only [icosahedral_card] using icosahedral_card_options t

end Holant.Certificates.PlatonicIncidence
