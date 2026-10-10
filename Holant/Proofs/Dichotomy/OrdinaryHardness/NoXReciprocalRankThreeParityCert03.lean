import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_24 : ∀n : Fin 128, 24≠127 → n.val≠127 → n.val≠127-24 →
    dot 24 (selector 24 n)=0 ∧ dot n (selector 24 n)=0 := by decide

theorem selected_25 : ∀n : Fin 128, 25≠127 → n.val≠127 → n.val≠127-25 →
    dot 25 (selector 25 n)=0 ∧ dot n (selector 25 n)=0 := by decide

theorem selected_26 : ∀n : Fin 128, 26≠127 → n.val≠127 → n.val≠127-26 →
    dot 26 (selector 26 n)=0 ∧ dot n (selector 26 n)=0 := by decide

theorem selected_27 : ∀n : Fin 128, 27≠127 → n.val≠127 → n.val≠127-27 →
    dot 27 (selector 27 n)=0 ∧ dot n (selector 27 n)=0 := by decide

theorem selected_28 : ∀n : Fin 128, 28≠127 → n.val≠127 → n.val≠127-28 →
    dot 28 (selector 28 n)=0 ∧ dot n (selector 28 n)=0 := by decide

theorem selected_29 : ∀n : Fin 128, 29≠127 → n.val≠127 → n.val≠127-29 →
    dot 29 (selector 29 n)=0 ∧ dot n (selector 29 n)=0 := by decide

theorem selected_30 : ∀n : Fin 128, 30≠127 → n.val≠127 → n.val≠127-30 →
    dot 30 (selector 30 n)=0 ∧ dot n (selector 30 n)=0 := by decide

theorem selected_31 : ∀n : Fin 128, 31≠127 → n.val≠127 → n.val≠127-31 →
    dot 31 (selector 31 n)=0 ∧ dot n (selector 31 n)=0 := by decide

theorem column_12 : ∀i j : Fin 7,column 12 i j=if functional 12 i then 1 else 0 := by decide

theorem column_13 : ∀i j : Fin 7,column 13 i j=if functional 13 i then 1 else 0 := by decide

theorem column_14 : ∀i j : Fin 7,column 14 i j=if functional 14 i then 1 else 0 := by decide

theorem column_15 : ∀i j : Fin 7,column 15 i j=if functional 15 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
