import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_96 : ∀n : Fin 128, 96≠127 → n.val≠127 → n.val≠127-96 →
    dot 96 (selector 96 n)=0 ∧ dot n (selector 96 n)=0 := by decide

theorem selected_97 : ∀n : Fin 128, 97≠127 → n.val≠127 → n.val≠127-97 →
    dot 97 (selector 97 n)=0 ∧ dot n (selector 97 n)=0 := by decide

theorem selected_98 : ∀n : Fin 128, 98≠127 → n.val≠127 → n.val≠127-98 →
    dot 98 (selector 98 n)=0 ∧ dot n (selector 98 n)=0 := by decide

theorem selected_99 : ∀n : Fin 128, 99≠127 → n.val≠127 → n.val≠127-99 →
    dot 99 (selector 99 n)=0 ∧ dot n (selector 99 n)=0 := by decide

theorem selected_100 : ∀n : Fin 128, 100≠127 → n.val≠127 → n.val≠127-100 →
    dot 100 (selector 100 n)=0 ∧ dot n (selector 100 n)=0 := by decide

theorem selected_101 : ∀n : Fin 128, 101≠127 → n.val≠127 → n.val≠127-101 →
    dot 101 (selector 101 n)=0 ∧ dot n (selector 101 n)=0 := by decide

theorem selected_102 : ∀n : Fin 128, 102≠127 → n.val≠127 → n.val≠127-102 →
    dot 102 (selector 102 n)=0 ∧ dot n (selector 102 n)=0 := by decide

theorem selected_103 : ∀n : Fin 128, 103≠127 → n.val≠127 → n.val≠127-103 →
    dot 103 (selector 103 n)=0 ∧ dot n (selector 103 n)=0 := by decide

theorem column_48 : ∀i j : Fin 7,column 48 i j=if functional 48 i then 1 else 0 := by decide

theorem column_49 : ∀i j : Fin 7,column 49 i j=if functional 49 i then 1 else 0 := by decide

theorem column_50 : ∀i j : Fin 7,column 50 i j=if functional 50 i then 1 else 0 := by decide

theorem column_51 : ∀i j : Fin 7,column 51 i j=if functional 51 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
