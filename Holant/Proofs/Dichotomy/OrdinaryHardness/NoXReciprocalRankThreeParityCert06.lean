import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_48 : ∀n : Fin 128, 48≠127 → n.val≠127 → n.val≠127-48 →
    dot 48 (selector 48 n)=0 ∧ dot n (selector 48 n)=0 := by decide

theorem selected_49 : ∀n : Fin 128, 49≠127 → n.val≠127 → n.val≠127-49 →
    dot 49 (selector 49 n)=0 ∧ dot n (selector 49 n)=0 := by decide

theorem selected_50 : ∀n : Fin 128, 50≠127 → n.val≠127 → n.val≠127-50 →
    dot 50 (selector 50 n)=0 ∧ dot n (selector 50 n)=0 := by decide

theorem selected_51 : ∀n : Fin 128, 51≠127 → n.val≠127 → n.val≠127-51 →
    dot 51 (selector 51 n)=0 ∧ dot n (selector 51 n)=0 := by decide

theorem selected_52 : ∀n : Fin 128, 52≠127 → n.val≠127 → n.val≠127-52 →
    dot 52 (selector 52 n)=0 ∧ dot n (selector 52 n)=0 := by decide

theorem selected_53 : ∀n : Fin 128, 53≠127 → n.val≠127 → n.val≠127-53 →
    dot 53 (selector 53 n)=0 ∧ dot n (selector 53 n)=0 := by decide

theorem selected_54 : ∀n : Fin 128, 54≠127 → n.val≠127 → n.val≠127-54 →
    dot 54 (selector 54 n)=0 ∧ dot n (selector 54 n)=0 := by decide

theorem selected_55 : ∀n : Fin 128, 55≠127 → n.val≠127 → n.val≠127-55 →
    dot 55 (selector 55 n)=0 ∧ dot n (selector 55 n)=0 := by decide

theorem column_24 : ∀i j : Fin 7,column 24 i j=if functional 24 i then 1 else 0 := by decide

theorem column_25 : ∀i j : Fin 7,column 25 i j=if functional 25 i then 1 else 0 := by decide

theorem column_26 : ∀i j : Fin 7,column 26 i j=if functional 26 i then 1 else 0 := by decide

theorem column_27 : ∀i j : Fin 7,column 27 i j=if functional 27 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
