import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_32 : ∀n : Fin 128, 32≠127 → n.val≠127 → n.val≠127-32 →
    dot 32 (selector 32 n)=0 ∧ dot n (selector 32 n)=0 := by decide

theorem selected_33 : ∀n : Fin 128, 33≠127 → n.val≠127 → n.val≠127-33 →
    dot 33 (selector 33 n)=0 ∧ dot n (selector 33 n)=0 := by decide

theorem selected_34 : ∀n : Fin 128, 34≠127 → n.val≠127 → n.val≠127-34 →
    dot 34 (selector 34 n)=0 ∧ dot n (selector 34 n)=0 := by decide

theorem selected_35 : ∀n : Fin 128, 35≠127 → n.val≠127 → n.val≠127-35 →
    dot 35 (selector 35 n)=0 ∧ dot n (selector 35 n)=0 := by decide

theorem selected_36 : ∀n : Fin 128, 36≠127 → n.val≠127 → n.val≠127-36 →
    dot 36 (selector 36 n)=0 ∧ dot n (selector 36 n)=0 := by decide

theorem selected_37 : ∀n : Fin 128, 37≠127 → n.val≠127 → n.val≠127-37 →
    dot 37 (selector 37 n)=0 ∧ dot n (selector 37 n)=0 := by decide

theorem selected_38 : ∀n : Fin 128, 38≠127 → n.val≠127 → n.val≠127-38 →
    dot 38 (selector 38 n)=0 ∧ dot n (selector 38 n)=0 := by decide

theorem selected_39 : ∀n : Fin 128, 39≠127 → n.val≠127 → n.val≠127-39 →
    dot 39 (selector 39 n)=0 ∧ dot n (selector 39 n)=0 := by decide

theorem column_16 : ∀i j : Fin 7,column 16 i j=if functional 16 i then 1 else 0 := by decide

theorem column_17 : ∀i j : Fin 7,column 17 i j=if functional 17 i then 1 else 0 := by decide

theorem column_18 : ∀i j : Fin 7,column 18 i j=if functional 18 i then 1 else 0 := by decide

theorem column_19 : ∀i j : Fin 7,column 19 i j=if functional 19 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
