import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_16 : ∀n : Fin 128, 16≠127 → n.val≠127 → n.val≠127-16 →
    dot 16 (selector 16 n)=0 ∧ dot n (selector 16 n)=0 := by decide

theorem selected_17 : ∀n : Fin 128, 17≠127 → n.val≠127 → n.val≠127-17 →
    dot 17 (selector 17 n)=0 ∧ dot n (selector 17 n)=0 := by decide

theorem selected_18 : ∀n : Fin 128, 18≠127 → n.val≠127 → n.val≠127-18 →
    dot 18 (selector 18 n)=0 ∧ dot n (selector 18 n)=0 := by decide

theorem selected_19 : ∀n : Fin 128, 19≠127 → n.val≠127 → n.val≠127-19 →
    dot 19 (selector 19 n)=0 ∧ dot n (selector 19 n)=0 := by decide

theorem selected_20 : ∀n : Fin 128, 20≠127 → n.val≠127 → n.val≠127-20 →
    dot 20 (selector 20 n)=0 ∧ dot n (selector 20 n)=0 := by decide

theorem selected_21 : ∀n : Fin 128, 21≠127 → n.val≠127 → n.val≠127-21 →
    dot 21 (selector 21 n)=0 ∧ dot n (selector 21 n)=0 := by decide

theorem selected_22 : ∀n : Fin 128, 22≠127 → n.val≠127 → n.val≠127-22 →
    dot 22 (selector 22 n)=0 ∧ dot n (selector 22 n)=0 := by decide

theorem selected_23 : ∀n : Fin 128, 23≠127 → n.val≠127 → n.val≠127-23 →
    dot 23 (selector 23 n)=0 ∧ dot n (selector 23 n)=0 := by decide

theorem column_8 : ∀i j : Fin 7,column 8 i j=if functional 8 i then 1 else 0 := by decide

theorem column_9 : ∀i j : Fin 7,column 9 i j=if functional 9 i then 1 else 0 := by decide

theorem column_10 : ∀i j : Fin 7,column 10 i j=if functional 10 i then 1 else 0 := by decide

theorem column_11 : ∀i j : Fin 7,column 11 i j=if functional 11 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
