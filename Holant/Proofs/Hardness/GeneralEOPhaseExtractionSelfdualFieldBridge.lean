import Holant.Proofs.Hardness.GeneralEOPhaseExtractionMatchingSwitch
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionFieldBridge

/-! The unsigned selfdual extraction returns an actual graph in the original
coefficient field. Complex phase decisions never add a coefficient or vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSelfdualFieldBridge
open Holant Holant.Complexity FixedGadgetSubstitution
namespace F
export GeneralEOPhaseExtractionFieldBridge (family map_exact map_native map_central
  rebuild labels rebuild_exact rebuild_native rebuild_central map_rebuild)
end F
namespace M
export GeneralEOPhaseExtractionMatchingSwitch (PositivePattern exists_nonpositive_quaternary_any)
end M
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature K (a i.val)) (φ : K→+*ℂ)

theorem nonpositive_quaternary (S : Network K n) (SL : Labelling S.shape s 1 a)
    (hL : LabelledNetwork.Exact G S SL) (hN : ∀e,S.edge e=Signature.disequality)
    (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual (S.map φ).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (S.map φ).denote) :
    ∃ (Q : Network K 4) (QL : Labelling Q.shape s 1 a),
      LabelledNetwork.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      Signature.CentralSupport Q.denote ∧ SelfDualPinObstruction.SelfDual Q.denote ∧
      ¬M.PositivePattern (Q.map φ).denote := by
  obtain ⟨Q,QL,hQL,hQN,hQE,hQS,hQP⟩ := M.exists_nonpositive_quaternary_any
    (F.family G φ) (S.map φ) SL (F.map_exact G φ S SL hL) (F.map_native φ S hN)
    (F.map_central φ S hE) hS hA
  refine ⟨F.rebuild G Q QL,F.labels G Q QL,F.rebuild_exact G Q QL,F.rebuild_native G Q QL,
    F.rebuild_central G φ Q QL hQL hQN hQE,?_,?_⟩
  · intro x
    apply φ.injective
    rw [←Network.denote_map φ,←Network.denote_map φ,F.map_rebuild G φ Q QL hQL hQN]
    exact hQS x
  · rw [F.map_rebuild G φ Q QL hQL hQN]
    exact hQP

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSelfdualFieldBridge
