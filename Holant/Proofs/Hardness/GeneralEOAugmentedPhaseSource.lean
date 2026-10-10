import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalOriginalField
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionControlledSource

/-! An adjoined binary row is an actual corolla over the augmented dictionary.
The original source retains its exact labels, so its common-sign non-ARS exit
is available whenever that literal row has the four signed-cap values. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAugmentedPhaseSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace A
export GeneralEOTensorPowerRemovalOriginalField (family family_old family_new oldLabel newLabel)
end A
namespace R
export GeneralEOTensorPowerRemovalRaw (sourceArity)
end R
namespace P
export GeneralEOPhaseExtractionSource (inclusion Pinning)
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard pinning_or_controlled_hardness)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (f : Signature AlgebraicComplex 2)

abbrev augmented := A.family G f

variable (S : Network AlgebraicComplex n) (SL : Labelling S.shape s 1 a)

def labels : Labelling S.shape (s+1) 1 (R.sourceArity s 2 a) where
  vertex v := A.oldLabel (SL.vertex v)
  vertex_arity v := by
    change R.sourceArity s 2 a (SL.vertex v).val=S.shape.arity v
    rw [R.sourceArity,ite_eq_left (SL.vertex v).isLt]
    exact SL.vertex_arity v
  edge := SL.edge

theorem exact (hS : LabelledNetwork.Exact G S SL) :
    LabelledNetwork.Exact (augmented G f) S (labels S SL) := by
  intro v
  exact (A.family_old G f (SL.vertex v)).trans (hS v)

abbrev cap : Network AlgebraicComplex 2 := Network.corolla f

def capLabels : Labelling (cap f).shape (s+1) 1 (R.sourceArity s 2 a) where
  vertex _ := A.newLabel
  vertex_arity _ := by simp [R.sourceArity,A.newLabel,cap,Network.corolla]
  edge e := Fin.elim0 e

theorem cap_exact : LabelledNetwork.Exact (augmented G f) (cap f) (capLabels f (s:=s) (a:=a)) := by
  intro v
  exact A.family_new G f

theorem cap_native : ∀e,(cap f).edge e=Signature.disequality := fun e => Fin.elim0 e

/-- No new source graph or free physical binary cap is assumed over G. -/
theorem alternative (hf : GeneralEOPhaseExtractionNetwork.Signed ((cap f).map P.inclusion) 1)
    (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign (S.map P.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (S.map P.inclusion).denote) :
    P.Pinning (augmented G f) ∨ P.ControlledCountingHard (augmented G f) :=
  P.pinning_or_controlled_hardness (augmented G f) (cap f) (capLabels f (s:=s) (a:=a))
    (cap_exact G f) (cap_native f) 1 (by norm_num) hf
    S (labels S SL) (exact G f S SL hL) hN hE hSign hA

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAugmentedPhaseSource
