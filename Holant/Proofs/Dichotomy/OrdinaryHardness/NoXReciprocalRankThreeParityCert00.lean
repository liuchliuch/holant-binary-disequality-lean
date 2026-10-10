import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_0 : ∀n : Fin 128, 0≠127 → n.val≠127 → n.val≠127-0 →
    dot 0 (selector 0 n)=0 ∧ dot n (selector 0 n)=0 := by decide

theorem selected_1 : ∀n : Fin 128, 1≠127 → n.val≠127 → n.val≠127-1 →
    dot 1 (selector 1 n)=0 ∧ dot n (selector 1 n)=0 := by decide

theorem selected_2 : ∀n : Fin 128, 2≠127 → n.val≠127 → n.val≠127-2 →
    dot 2 (selector 2 n)=0 ∧ dot n (selector 2 n)=0 := by decide

theorem selected_3 : ∀n : Fin 128, 3≠127 → n.val≠127 → n.val≠127-3 →
    dot 3 (selector 3 n)=0 ∧ dot n (selector 3 n)=0 := by decide

theorem selected_4 : ∀n : Fin 128, 4≠127 → n.val≠127 → n.val≠127-4 →
    dot 4 (selector 4 n)=0 ∧ dot n (selector 4 n)=0 := by decide

theorem selected_5 : ∀n : Fin 128, 5≠127 → n.val≠127 → n.val≠127-5 →
    dot 5 (selector 5 n)=0 ∧ dot n (selector 5 n)=0 := by decide

theorem selected_6 : ∀n : Fin 128, 6≠127 → n.val≠127 → n.val≠127-6 →
    dot 6 (selector 6 n)=0 ∧ dot n (selector 6 n)=0 := by decide

theorem selected_7 : ∀n : Fin 128, 7≠127 → n.val≠127 → n.val≠127-7 →
    dot 7 (selector 7 n)=0 ∧ dot n (selector 7 n)=0 := by decide

theorem column_0 : ∀i j : Fin 7,column 0 i j=if functional 0 i then 1 else 0 := by decide

theorem column_1 : ∀i j : Fin 7,column 1 i j=if functional 1 i then 1 else 0 := by decide

theorem column_2 : ∀i j : Fin 7,column 2 i j=if functional 2 i then 1 else 0 := by decide

theorem column_3 : ∀i j : Fin 7,column 3 i j=if functional 3 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
