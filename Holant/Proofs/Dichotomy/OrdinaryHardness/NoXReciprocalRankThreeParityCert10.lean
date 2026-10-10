import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_80 : ∀n : Fin 128, 80≠127 → n.val≠127 → n.val≠127-80 →
    dot 80 (selector 80 n)=0 ∧ dot n (selector 80 n)=0 := by decide

theorem selected_81 : ∀n : Fin 128, 81≠127 → n.val≠127 → n.val≠127-81 →
    dot 81 (selector 81 n)=0 ∧ dot n (selector 81 n)=0 := by decide

theorem selected_82 : ∀n : Fin 128, 82≠127 → n.val≠127 → n.val≠127-82 →
    dot 82 (selector 82 n)=0 ∧ dot n (selector 82 n)=0 := by decide

theorem selected_83 : ∀n : Fin 128, 83≠127 → n.val≠127 → n.val≠127-83 →
    dot 83 (selector 83 n)=0 ∧ dot n (selector 83 n)=0 := by decide

theorem selected_84 : ∀n : Fin 128, 84≠127 → n.val≠127 → n.val≠127-84 →
    dot 84 (selector 84 n)=0 ∧ dot n (selector 84 n)=0 := by decide

theorem selected_85 : ∀n : Fin 128, 85≠127 → n.val≠127 → n.val≠127-85 →
    dot 85 (selector 85 n)=0 ∧ dot n (selector 85 n)=0 := by decide

theorem selected_86 : ∀n : Fin 128, 86≠127 → n.val≠127 → n.val≠127-86 →
    dot 86 (selector 86 n)=0 ∧ dot n (selector 86 n)=0 := by decide

theorem selected_87 : ∀n : Fin 128, 87≠127 → n.val≠127 → n.val≠127-87 →
    dot 87 (selector 87 n)=0 ∧ dot n (selector 87 n)=0 := by decide

theorem column_40 : ∀i j : Fin 7,column 40 i j=if functional 40 i then 1 else 0 := by decide

theorem column_41 : ∀i j : Fin 7,column 41 i j=if functional 41 i then 1 else 0 := by decide

theorem column_42 : ∀i j : Fin 7,column 42 i j=if functional 42 i then 1 else 0 := by decide

theorem column_43 : ∀i j : Fin 7,column 43 i j=if functional 43 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
