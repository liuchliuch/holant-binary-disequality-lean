import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_8 : ∀n : Fin 128, 8≠127 → n.val≠127 → n.val≠127-8 →
    dot 8 (selector 8 n)=0 ∧ dot n (selector 8 n)=0 := by decide

theorem selected_9 : ∀n : Fin 128, 9≠127 → n.val≠127 → n.val≠127-9 →
    dot 9 (selector 9 n)=0 ∧ dot n (selector 9 n)=0 := by decide

theorem selected_10 : ∀n : Fin 128, 10≠127 → n.val≠127 → n.val≠127-10 →
    dot 10 (selector 10 n)=0 ∧ dot n (selector 10 n)=0 := by decide

theorem selected_11 : ∀n : Fin 128, 11≠127 → n.val≠127 → n.val≠127-11 →
    dot 11 (selector 11 n)=0 ∧ dot n (selector 11 n)=0 := by decide

theorem selected_12 : ∀n : Fin 128, 12≠127 → n.val≠127 → n.val≠127-12 →
    dot 12 (selector 12 n)=0 ∧ dot n (selector 12 n)=0 := by decide

theorem selected_13 : ∀n : Fin 128, 13≠127 → n.val≠127 → n.val≠127-13 →
    dot 13 (selector 13 n)=0 ∧ dot n (selector 13 n)=0 := by decide

theorem selected_14 : ∀n : Fin 128, 14≠127 → n.val≠127 → n.val≠127-14 →
    dot 14 (selector 14 n)=0 ∧ dot n (selector 14 n)=0 := by decide

theorem selected_15 : ∀n : Fin 128, 15≠127 → n.val≠127 → n.val≠127-15 →
    dot 15 (selector 15 n)=0 ∧ dot n (selector 15 n)=0 := by decide

theorem column_4 : ∀i j : Fin 7,column 4 i j=if functional 4 i then 1 else 0 := by decide

theorem column_5 : ∀i j : Fin 7,column 5 i j=if functional 5 i then 1 else 0 := by decide

theorem column_6 : ∀i j : Fin 7,column 6 i j=if functional 6 i then 1 else 0 := by decide

theorem column_7 : ∀i j : Fin 7,column 7 i j=if functional 7 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
