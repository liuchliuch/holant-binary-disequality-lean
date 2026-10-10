import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_72 : ∀n : Fin 128, 72≠127 → n.val≠127 → n.val≠127-72 →
    dot 72 (selector 72 n)=0 ∧ dot n (selector 72 n)=0 := by decide

theorem selected_73 : ∀n : Fin 128, 73≠127 → n.val≠127 → n.val≠127-73 →
    dot 73 (selector 73 n)=0 ∧ dot n (selector 73 n)=0 := by decide

theorem selected_74 : ∀n : Fin 128, 74≠127 → n.val≠127 → n.val≠127-74 →
    dot 74 (selector 74 n)=0 ∧ dot n (selector 74 n)=0 := by decide

theorem selected_75 : ∀n : Fin 128, 75≠127 → n.val≠127 → n.val≠127-75 →
    dot 75 (selector 75 n)=0 ∧ dot n (selector 75 n)=0 := by decide

theorem selected_76 : ∀n : Fin 128, 76≠127 → n.val≠127 → n.val≠127-76 →
    dot 76 (selector 76 n)=0 ∧ dot n (selector 76 n)=0 := by decide

theorem selected_77 : ∀n : Fin 128, 77≠127 → n.val≠127 → n.val≠127-77 →
    dot 77 (selector 77 n)=0 ∧ dot n (selector 77 n)=0 := by decide

theorem selected_78 : ∀n : Fin 128, 78≠127 → n.val≠127 → n.val≠127-78 →
    dot 78 (selector 78 n)=0 ∧ dot n (selector 78 n)=0 := by decide

theorem selected_79 : ∀n : Fin 128, 79≠127 → n.val≠127 → n.val≠127-79 →
    dot 79 (selector 79 n)=0 ∧ dot n (selector 79 n)=0 := by decide

theorem column_36 : ∀i j : Fin 7,column 36 i j=if functional 36 i then 1 else 0 := by decide

theorem column_37 : ∀i j : Fin 7,column 37 i j=if functional 37 i then 1 else 0 := by decide

theorem column_38 : ∀i j : Fin 7,column 38 i j=if functional 38 i then 1 else 0 := by decide

theorem column_39 : ∀i j : Fin 7,column 39 i j=if functional 39 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
