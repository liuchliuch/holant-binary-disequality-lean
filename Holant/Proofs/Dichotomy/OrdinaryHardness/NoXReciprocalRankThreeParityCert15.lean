import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_120 : ∀n : Fin 128, 120≠127 → n.val≠127 → n.val≠127-120 →
    dot 120 (selector 120 n)=0 ∧ dot n (selector 120 n)=0 := by decide

theorem selected_121 : ∀n : Fin 128, 121≠127 → n.val≠127 → n.val≠127-121 →
    dot 121 (selector 121 n)=0 ∧ dot n (selector 121 n)=0 := by decide

theorem selected_122 : ∀n : Fin 128, 122≠127 → n.val≠127 → n.val≠127-122 →
    dot 122 (selector 122 n)=0 ∧ dot n (selector 122 n)=0 := by decide

theorem selected_123 : ∀n : Fin 128, 123≠127 → n.val≠127 → n.val≠127-123 →
    dot 123 (selector 123 n)=0 ∧ dot n (selector 123 n)=0 := by decide

theorem selected_124 : ∀n : Fin 128, 124≠127 → n.val≠127 → n.val≠127-124 →
    dot 124 (selector 124 n)=0 ∧ dot n (selector 124 n)=0 := by decide

theorem selected_125 : ∀n : Fin 128, 125≠127 → n.val≠127 → n.val≠127-125 →
    dot 125 (selector 125 n)=0 ∧ dot n (selector 125 n)=0 := by decide

theorem selected_126 : ∀n : Fin 128, 126≠127 → n.val≠127 → n.val≠127-126 →
    dot 126 (selector 126 n)=0 ∧ dot n (selector 126 n)=0 := by decide

theorem selected_127 : ∀n : Fin 128, 127≠127 → n.val≠127 → n.val≠127-127 →
    dot 127 (selector 127 n)=0 ∧ dot n (selector 127 n)=0 := by decide

theorem column_60 : ∀i j : Fin 7,column 60 i j=if functional 60 i then 1 else 0 := by decide

theorem column_61 : ∀i j : Fin 7,column 61 i j=if functional 61 i then 1 else 0 := by decide

theorem column_62 : ∀i j : Fin 7,column 62 i j=if functional 62 i then 1 else 0 := by decide

theorem column_63 : ∀i j : Fin 7,column 63 i j=if functional 63 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
