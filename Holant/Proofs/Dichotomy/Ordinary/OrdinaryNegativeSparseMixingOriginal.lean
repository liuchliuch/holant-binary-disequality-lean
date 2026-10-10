import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicOriginal

/-! Every literal sparse mixing block is a physical source into the unchanged
original G. This composes the fixed-field private-sum compiler with the actual
anchor/pin source; no compressed-signature oracle or new field is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export StableHigherCurrentEvenCSPSource (current ordinary ordinaryArity field eq4Label eq4_literal)
end S
namespace Pn
export OrdinaryNegativeCubicOriginal (falseLabel trueLabel false_literal true_literal)
end Pn
namespace One
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K)
end One
namespace M
export OrdinaryNegativeSparseMixingSource (Block)
end M
namespace D
export OrdinaryNegativeMixedBlockData (inputEncoding)
export OrdinaryNegativeMixedBlockSource (privateValue)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (A : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (S.current G P)))
local instance : Algebra ℚ (One.K (S.current G P) A) := (One.K (S.current G P) A).algebra'
variable {n : ℕ}

def source (B : M.Block (s:=P.count+3) (b:=S.ordinaryArity G P A) n) :
    PhysicalProgramme (D.inputEncoding (u:=1) (a:=fun _=>n)) (S.field G P A).encoding
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding
      (D.privateValue (S.ordinary G P A) B.privateCount B.rows)
      (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (B.controlled (S.ordinary G P A) (S.field G P A)
      (S.eq4Label G P) (Pn.falseLabel G P) (Pn.trueLabel G P)
      (S.eq4_literal G P A) (Pn.false_literal G P A) (Pn.true_literal G P A))
    (StableHigherCurrentAnchorPins.toOriginal G P A).controlled)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingOriginal
end
