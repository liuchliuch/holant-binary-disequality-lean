import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_56 : ∀n : Fin 128, 56≠127 → n.val≠127 → n.val≠127-56 →
    dot 56 (selector 56 n)=0 ∧ dot n (selector 56 n)=0 := by decide

theorem selected_57 : ∀n : Fin 128, 57≠127 → n.val≠127 → n.val≠127-57 →
    dot 57 (selector 57 n)=0 ∧ dot n (selector 57 n)=0 := by decide

theorem selected_58 : ∀n : Fin 128, 58≠127 → n.val≠127 → n.val≠127-58 →
    dot 58 (selector 58 n)=0 ∧ dot n (selector 58 n)=0 := by decide

theorem selected_59 : ∀n : Fin 128, 59≠127 → n.val≠127 → n.val≠127-59 →
    dot 59 (selector 59 n)=0 ∧ dot n (selector 59 n)=0 := by decide

theorem selected_60 : ∀n : Fin 128, 60≠127 → n.val≠127 → n.val≠127-60 →
    dot 60 (selector 60 n)=0 ∧ dot n (selector 60 n)=0 := by decide

theorem selected_61 : ∀n : Fin 128, 61≠127 → n.val≠127 → n.val≠127-61 →
    dot 61 (selector 61 n)=0 ∧ dot n (selector 61 n)=0 := by decide

theorem selected_62 : ∀n : Fin 128, 62≠127 → n.val≠127 → n.val≠127-62 →
    dot 62 (selector 62 n)=0 ∧ dot n (selector 62 n)=0 := by decide

theorem selected_63 : ∀n : Fin 128, 63≠127 → n.val≠127 → n.val≠127-63 →
    dot 63 (selector 63 n)=0 ∧ dot n (selector 63 n)=0 := by decide

theorem column_28 : ∀i j : Fin 7,column 28 i j=if functional 28 i then 1 else 0 := by decide

theorem column_29 : ∀i j : Fin 7,column 29 i j=if functional 29 i then 1 else 0 := by decide

theorem column_30 : ∀i j : Fin 7,column 30 i j=if functional 30 i then 1 else 0 := by decide

theorem column_31 : ∀i j : Fin 7,column 31 i j=if functional 31 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
