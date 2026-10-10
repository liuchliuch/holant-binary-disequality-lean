import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem selected_112 : ∀n : Fin 128, 112≠127 → n.val≠127 → n.val≠127-112 →
    dot 112 (selector 112 n)=0 ∧ dot n (selector 112 n)=0 := by decide

theorem selected_113 : ∀n : Fin 128, 113≠127 → n.val≠127 → n.val≠127-113 →
    dot 113 (selector 113 n)=0 ∧ dot n (selector 113 n)=0 := by decide

theorem selected_114 : ∀n : Fin 128, 114≠127 → n.val≠127 → n.val≠127-114 →
    dot 114 (selector 114 n)=0 ∧ dot n (selector 114 n)=0 := by decide

theorem selected_115 : ∀n : Fin 128, 115≠127 → n.val≠127 → n.val≠127-115 →
    dot 115 (selector 115 n)=0 ∧ dot n (selector 115 n)=0 := by decide

theorem selected_116 : ∀n : Fin 128, 116≠127 → n.val≠127 → n.val≠127-116 →
    dot 116 (selector 116 n)=0 ∧ dot n (selector 116 n)=0 := by decide

theorem selected_117 : ∀n : Fin 128, 117≠127 → n.val≠127 → n.val≠127-117 →
    dot 117 (selector 117 n)=0 ∧ dot n (selector 117 n)=0 := by decide

theorem selected_118 : ∀n : Fin 128, 118≠127 → n.val≠127 → n.val≠127-118 →
    dot 118 (selector 118 n)=0 ∧ dot n (selector 118 n)=0 := by decide

theorem selected_119 : ∀n : Fin 128, 119≠127 → n.val≠127 → n.val≠127-119 →
    dot 119 (selector 119 n)=0 ∧ dot n (selector 119 n)=0 := by decide

theorem column_56 : ∀i j : Fin 7,column 56 i j=if functional 56 i then 1 else 0 := by decide

theorem column_57 : ∀i j : Fin 7,column 57 i j=if functional 57 i then 1 else 0 := by decide

theorem column_58 : ∀i j : Fin 7,column 58 i j=if functional 58 i then 1 else 0 := by decide

theorem column_59 : ∀i j : Fin 7,column 59 i j=if functional 59 i then 1 else 0 := by decide

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
