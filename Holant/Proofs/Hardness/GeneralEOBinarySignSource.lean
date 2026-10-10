import Holant.Proofs.Hardness.GeneralEOBinarySignNetwork
import Holant.Proofs.Hardness.GeneralEOGeneralPhaseBinarySource

/-! Original-field exit for the generated order-two binary residual. All
quantified binaries remain actual graphs with the unchanged original labels. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace S
export GeneralEOPhaseExtractionSource (inclusion CountingHard)
end S
namespace B
export GeneralEOPhaseExtractionFieldBridge (family map_exact map_native map_central
  rebuild labels rebuild_exact rebuild_native rebuild_central map_rebuild)
end B
namespace N
export GeneralEOBinarySignNetwork (BinarySquare sign_of_binary_square)
end N
set_option backward.isDefEq.respectTransparency false
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

def BinarySquare : Prop := ∀ (Q : Network AlgebraicComplex 2) (QL : Labelling Q.shape s 1 a),
  LabelledNetwork.Exact G Q QL → (∀e,Q.edge e=Signature.disequality) →
  Signature.CentralSupport Q.denote → Q.denote ![false,true]^2=Q.denote ![true,false]^2

theorem binary_square_map (h : BinarySquare G) : N.BinarySquare (B.family G S.inclusion) := by
  intro Q QL hL hN hE
  let U := B.rebuild G Q QL
  have hh := h U (B.labels G Q QL) (B.rebuild_exact G Q QL)
    (B.rebuild_native G Q QL) (B.rebuild_central G S.inclusion Q QL hL hN hE)
  have hh' := congrArg S.inclusion hh
  simp only [map_pow] at hh'
  rw [←Network.denote_map,←Network.denote_map] at hh'
  simpa only [U,B.map_rebuild G S.inclusion Q QL hL hN] using hh'

theorem sign (h : BinarySquare G) (T : Network AlgebraicComplex n)
    (TL : Labelling T.shape s 1 a) (hL : LabelledNetwork.Exact G T TL)
    (hN : ∀e,T.edge e=Signature.disequality) (hE : Signature.CentralSupport T.denote) :
    GeneralEOPhaseExtractionSigns.Sign (T.map S.inclusion).denote :=
  N.sign_of_binary_square (B.family G S.inclusion) (binary_square_map G h)
    (T.map S.inclusion) TL (B.map_exact G S.inclusion T TL hL)
    (B.map_native S.inclusion T hN) (B.map_central S.inclusion T hE)

theorem pinning_or_hardness (h : BinarySquare G) (T : Network AlgebraicComplex n)
    (TL : Labelling T.shape s 1 a) (hL : LabelledNetwork.Exact G T TL)
    (hN : ∀e,T.edge e=Signature.disequality) (hE : Signature.CentralSupport T.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.CountingHard G :=
  GeneralEOSkewPhaseSource.pinning_or_hardness G T TL hL hN hE
    (sign G h T TL hL hN hE) hA

/-- Failure of original pin elimination constrains every generated central
binary's opposite norms, not merely caps of one original row. -/
theorem binary_norms_of_no_elimination
    (hp : ¬Nonempty (GeneralEOPinEliminationCases.Elimination G))
    (Q : Network AlgebraicComplex 2) (QL : Labelling Q.shape s 1 a)
    (hL : LabelledNetwork.Exact G Q QL) (hN : ∀e,Q.edge e=Signature.disequality)
    (hE : Signature.CentralSupport Q.denote) :
    ‖S.inclusion (Q.denote ![false,true])‖=‖S.inclusion (Q.denote ![true,false])‖ := by
  classical
  by_contra hn
  exact hp (GeneralEOGeneralPhaseBinarySource.unequal_norms G Q QL hL hN hE hn)

theorem binary_norms_map_of_no_elimination
    (hp : ¬Nonempty (GeneralEOPinEliminationCases.Elimination G))
    (Q : Network ℂ 2) (QL : Labelling Q.shape s 1 a)
    (hL : LabelledNetwork.Exact (B.family G S.inclusion) Q QL)
    (hN : ∀e,Q.edge e=Signature.disequality) (hE : Signature.CentralSupport Q.denote) :
    ‖Q.denote ![false,true]‖=‖Q.denote ![true,false]‖ := by
  let U := B.rebuild G Q QL
  have hh := binary_norms_of_no_elimination G hp U (B.labels G Q QL)
    (B.rebuild_exact G Q QL) (B.rebuild_native G Q QL)
    (B.rebuild_central G S.inclusion Q QL hL hN hE)
  rw [←Network.denote_map,←Network.denote_map] at hh
  simpa only [U,B.map_rebuild G S.inclusion Q QL hL hN] using hh


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignSource
