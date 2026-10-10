import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_64 : ∀n : Fin 128, 64≠127 → n.val≠127 → n.val≠127-64 →
    dot 64 (selector 64 n)=0 ∧ dot n (selector 64 n)=0 := by decide

theorem selected_65 : ∀n : Fin 128, 65≠127 → n.val≠127 → n.val≠127-65 →
    dot 65 (selector 65 n)=0 ∧ dot n (selector 65 n)=0 := by decide

theorem selected_66 : ∀n : Fin 128, 66≠127 → n.val≠127 → n.val≠127-66 →
    dot 66 (selector 66 n)=0 ∧ dot n (selector 66 n)=0 := by decide

theorem selected_67 : ∀n : Fin 128, 67≠127 → n.val≠127 → n.val≠127-67 →
    dot 67 (selector 67 n)=0 ∧ dot n (selector 67 n)=0 := by decide

theorem selected_68 : ∀n : Fin 128, 68≠127 → n.val≠127 → n.val≠127-68 →
    dot 68 (selector 68 n)=0 ∧ dot n (selector 68 n)=0 := by decide

theorem selected_69 : ∀n : Fin 128, 69≠127 → n.val≠127 → n.val≠127-69 →
    dot 69 (selector 69 n)=0 ∧ dot n (selector 69 n)=0 := by decide

theorem selected_70 : ∀n : Fin 128, 70≠127 → n.val≠127 → n.val≠127-70 →
    dot 70 (selector 70 n)=0 ∧ dot n (selector 70 n)=0 := by decide

theorem selected_71 : ∀n : Fin 128, 71≠127 → n.val≠127 → n.val≠127-71 →
    dot 71 (selector 71 n)=0 ∧ dot n (selector 71 n)=0 := by decide

theorem column_32 : ∀i j : Fin 7,column 32 i j=if functional 32 i then 1 else 0 := by decide

theorem column_33 : ∀i j : Fin 7,column 33 i j=if functional 33 i then 1 else 0 := by decide

theorem column_34 : ∀i j : Fin 7,column 34 i j=if functional 34 i then 1 else 0 := by decide

theorem column_35 : ∀i j : Fin 7,column 35 i j=if functional 35 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
