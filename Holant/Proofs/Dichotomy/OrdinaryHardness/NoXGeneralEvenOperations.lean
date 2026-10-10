import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenAntiSigned
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGadgetRecipe

/-! Tensor, signed support shifts and fixed extraction gadgets act on actual
even blocks while preserving every original private variable and row label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenOperations
open Holant Holant.Tractable
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace T
export OrdinaryNegativeAffineSupportTensorRecipe (recipe even_recipe trace_eq)
end T
namespace G
export OrdinaryNegativeAffineSupportGadgetRecipe (recipe privateCount even_recipe trace_eq)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end G
namespace S
export NoXGeneralEvenAntiSigned (block block_value)
end S
namespace E
export OrdinaryNegativeAffineSupportExtraction (combined shift)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s n m a : ℕ} {b : ℕ→ℕ}
variable (first : B.Block (s:=s) (b:=b) m) (second : B.Block (s:=s) (b:=b) n)

def tensor : B.Block (s:=s) (b:=b) (m+n) where
  privateCount := first.privateCount+second.privateCount
  rows := T.recipe first.rows second.rows
  balanced := T.even_recipe first.rows second.rows first.balanced second.balanced

def gadget (q : G.Gadget m a) : B.Block (s:=s) (b:=b) a where
  privateCount := G.privateCount (k:=first.privateCount) q
  rows := G.recipe q first.rows
  balanced := G.even_recipe q first.rows first.balanced

variable {K : Type} [Field K] (H : (j : Fin s)→Signature K (b j.val))

theorem tensor_value (x : Fin (m+n)→Bool) : (tensor first second).signature H x=
    first.signature H (fun i=>x (Fin.castAdd n i))*second.signature H (fun i=>x (Fin.natAdd m i)) :=
  T.trace_eq first.rows second.rows H x

theorem gadget_value (q : G.Gadget m a) (x : Fin a→Bool) :
    (gadget first q).signature H x=G.denote (first.signature H) q x := G.trace_eq q first.rows H x

variable (antiRow : B.Block (s:=s) (b:=b) 2) (left : Fin m→Bool) (right : Fin n→Bool)

def shiftedTensor : B.Block (s:=s) (b:=b) (m+n) :=
  S.block (tensor first second) antiRow (Fin.addCases left right)

variable [Algebra ℚ K] (v w : K) (anti : antiRow.signature H=NoXWeightedAntiSigned.anti v w)
include anti in
theorem shiftedTensor_value (x : Fin (m+n)→Bool) :
    (shiftedTensor first second antiRow left right).signature H x=
      (v*w)^(m+n)*E.combined (first.signature H) (second.signature H) left right x := by
  rw [shiftedTensor,S.block_value _ antiRow _ H v w anti,tensor_value]
  unfold E.combined E.shift OrdinaryNegativeNonproductBundleSupport.flip
  simp only [Fin.addCases_left,Fin.addCases_right]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenOperations
end
