import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroOrigin

/-! Original-G source for the opposite-pin alternative from any actual
zero-origin row or loop graph. All cap choices, the positive power, its
nonzero scalar, residue extraction, and answer codecs are produced inside.
The entire old family and its whole-family obstruction are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroOriginSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace V
export GeneralOddNonisotropicFrame (norm chart Ordinary)
end V
namespace Z
export GlobalCloseCompletionUnaryZeroOrigin (power)
export GlobalCloseCompletionUnaryZeroPower (opposite)
end Z
namespace P
export GlobalCloseCompletionUnaryPowerSource (toOriginal)
end P
namespace E
export GlobalCloseCompletionUnaryZeroSource (family vector old_included opposite_member independent)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree n : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (U : Network L 1) (UL : Labelling U.shape r 1 b)
variable (uExact : LabelledNetwork.Exact H U UL) (uEdges : V.Ordinary U)
variable (N : Network L n) (NL : Labelling N.shape r 1 b)
variable (nExact : LabelledNetwork.Exact H N NL) (nEdges : V.Ordinary N)
variable (hu : V.norm U.denote≠0) (nonzero : N.denote≠0)
variable (zero : V.chart U.denote N.denote (fun _=>false)=0)

def power := Z.power H U UL uExact uEdges N NL nExact nEdges hu nonzero zero
def source :=
  let D := power L H U UL uExact uEdges N NL nExact nEdges hu nonzero zero
  P.toOriginal G L F H back D.graph D.labels D.exact D.edges D.positive
    (Z.opposite U.denote) D.scalar D.nonzero D.equation

theorem obstruction (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H)) :
    ¬Tract (E.family L H U) :=
  fun positive=>negative (positive.mono_family (E.old_included L H U))

include hu in
theorem independent : GlobalCloseCompletionUnaryIsotropicSource.determinant
    (fun x=>(U.denote x : AlgebraicComplex)) (fun x=>E.vector L U (x 0))=1 :=
  E.independent L U hu


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroOriginSource
end
