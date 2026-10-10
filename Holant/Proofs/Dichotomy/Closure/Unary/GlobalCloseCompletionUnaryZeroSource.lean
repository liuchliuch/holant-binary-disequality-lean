import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPowerSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroPower

/-! Eliminate the zero own-axis endpoint by a genuine original-G source.
The exact original-field power identity feeds the checked power extractor,
which retains the whole old ordinary table and adds the literal perpendicular
unary. Independence is verified in the unchanged coordinates; no equality
anchor or terminal classification is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open BinaryCompose Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace Z
export GlobalCloseCompletionUnaryZeroPower (opposite exact_power independent)
end Z
namespace C
export GlobalCloseCompletionUnaryOrdinaryFieldCodec (ambient)
end C
namespace P
export GlobalCloseCompletionUnaryPowerOrdinary (family old_included unary_member)
export GlobalCloseCompletionUnaryPowerSource (toOriginal)
end P
namespace D
export GlobalCloseCompletionUnaryDescentSource (Endpoint)
end D
namespace U
export GeneralOddNonisotropicFrame (norm chart)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : Network L 1) (hu : U.norm N.denote≠0)
variable (D : D.Endpoint L H N) (zero : U.chart N.denote D.graph.denote (fun _=>false)=0)

abbrev vector : Bool→AlgebraicComplex := fun b=>((Z.opposite (K:=L) N.denote b : L) : AlgebraicComplex)
abbrev family := P.family (C.ambient L H) (vector L N)

def source := P.toOriginal G L F H back D.graph D.labels D.exact D.ordinary D.positive
  (Z.opposite N.denote) (U.chart N.denote D.graph.denote (fun _=>true)) D.opposite
  (Z.exact_power N.denote hu D.graph.denote D.support zero)

theorem old_included : GlobalCloseCompletionUnaryDescentSource.ambient L H⊆family L H N :=
  P.old_included (C.ambient L H) (vector L N)

theorem opposite_member : (⟨1,fun x=>vector L N (x 0)⟩ : AnySignature AlgebraicComplex)∈family L H N :=
  P.unary_member (C.ambient L H) (vector L N)

include hu in
theorem independent : GlobalCloseCompletionUnaryIsotropicSource.determinant
    (fun x=>(N.denote x : AlgebraicComplex)) (fun x=>vector L N (x 0))=1 := by
  have h := congrArg (fun z : L=>(z : AlgebraicComplex)) (Z.independent N.denote hu)
  change (L.subtype : L→+*AlgebraicComplex) (GlobalCloseCompletionUnaryIsotropicSource.determinant (K:=L) N.denote
    (fun x=>Z.opposite (K:=L) N.denote (x 0)))=(1 : AlgebraicComplex) at h
  simp only [GlobalCloseCompletionUnaryIsotropicSource.determinant,map_sub,map_mul,map_one] at h
  convert h using 1 <;> rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroSource
end
