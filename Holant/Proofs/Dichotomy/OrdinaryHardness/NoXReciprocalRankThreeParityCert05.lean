import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_40 : ∀n : Fin 128, 40≠127 → n.val≠127 → n.val≠127-40 →
    dot 40 (selector 40 n)=0 ∧ dot n (selector 40 n)=0 := by decide

theorem selected_41 : ∀n : Fin 128, 41≠127 → n.val≠127 → n.val≠127-41 →
    dot 41 (selector 41 n)=0 ∧ dot n (selector 41 n)=0 := by decide

theorem selected_42 : ∀n : Fin 128, 42≠127 → n.val≠127 → n.val≠127-42 →
    dot 42 (selector 42 n)=0 ∧ dot n (selector 42 n)=0 := by decide

theorem selected_43 : ∀n : Fin 128, 43≠127 → n.val≠127 → n.val≠127-43 →
    dot 43 (selector 43 n)=0 ∧ dot n (selector 43 n)=0 := by decide

theorem selected_44 : ∀n : Fin 128, 44≠127 → n.val≠127 → n.val≠127-44 →
    dot 44 (selector 44 n)=0 ∧ dot n (selector 44 n)=0 := by decide

theorem selected_45 : ∀n : Fin 128, 45≠127 → n.val≠127 → n.val≠127-45 →
    dot 45 (selector 45 n)=0 ∧ dot n (selector 45 n)=0 := by decide

theorem selected_46 : ∀n : Fin 128, 46≠127 → n.val≠127 → n.val≠127-46 →
    dot 46 (selector 46 n)=0 ∧ dot n (selector 46 n)=0 := by decide

theorem selected_47 : ∀n : Fin 128, 47≠127 → n.val≠127 → n.val≠127-47 →
    dot 47 (selector 47 n)=0 ∧ dot n (selector 47 n)=0 := by decide

theorem column_20 : ∀i j : Fin 7,column 20 i j=if functional 20 i then 1 else 0 := by decide

theorem column_21 : ∀i j : Fin 7,column 21 i j=if functional 21 i then 1 else 0 := by decide

theorem column_22 : ∀i j : Fin 7,column 22 i j=if functional 22 i then 1 else 0 := by decide

theorem column_23 : ∀i j : Fin 7,column 23 i j=if functional 23 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
