import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_104 : ∀n : Fin 128, 104≠127 → n.val≠127 → n.val≠127-104 →
    dot 104 (selector 104 n)=0 ∧ dot n (selector 104 n)=0 := by decide

theorem selected_105 : ∀n : Fin 128, 105≠127 → n.val≠127 → n.val≠127-105 →
    dot 105 (selector 105 n)=0 ∧ dot n (selector 105 n)=0 := by decide

theorem selected_106 : ∀n : Fin 128, 106≠127 → n.val≠127 → n.val≠127-106 →
    dot 106 (selector 106 n)=0 ∧ dot n (selector 106 n)=0 := by decide

theorem selected_107 : ∀n : Fin 128, 107≠127 → n.val≠127 → n.val≠127-107 →
    dot 107 (selector 107 n)=0 ∧ dot n (selector 107 n)=0 := by decide

theorem selected_108 : ∀n : Fin 128, 108≠127 → n.val≠127 → n.val≠127-108 →
    dot 108 (selector 108 n)=0 ∧ dot n (selector 108 n)=0 := by decide

theorem selected_109 : ∀n : Fin 128, 109≠127 → n.val≠127 → n.val≠127-109 →
    dot 109 (selector 109 n)=0 ∧ dot n (selector 109 n)=0 := by decide

theorem selected_110 : ∀n : Fin 128, 110≠127 → n.val≠127 → n.val≠127-110 →
    dot 110 (selector 110 n)=0 ∧ dot n (selector 110 n)=0 := by decide

theorem selected_111 : ∀n : Fin 128, 111≠127 → n.val≠127 → n.val≠127-111 →
    dot 111 (selector 111 n)=0 ∧ dot n (selector 111 n)=0 := by decide

theorem column_52 : ∀i j : Fin 7,column 52 i j=if functional 52 i then 1 else 0 := by decide

theorem column_53 : ∀i j : Fin 7,column 53 i j=if functional 53 i then 1 else 0 := by decide

theorem column_54 : ∀i j : Fin 7,column 54 i j=if functional 54 i then 1 else 0 := by decide

theorem column_55 : ∀i j : Fin 7,column 55 i j=if functional 55 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
