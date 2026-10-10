import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPowerOrdinary
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOrdinaryFieldCodec

/-! Original-G source adapter for the actual unary-power extractor. The old
fixed field is mapped faithfully to algebraic coefficients, the checked
ordinary power source is applied, and its real answer conversion is composed
with the original source. The entire old family and the literal unary remain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPowerSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open BinaryCompose Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace O
export GlobalCloseCompletionUnaryPowerOrdinary (field presentation table family controlled old_included unary_member)
end O
namespace C
export GlobalCloseCompletionUnaryOrdinaryFieldCodec (ambient controlled)
end C
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
variable (N : Network L n) (NL : Labelling N.shape r 1 b)
variable (exactN : LabelledNetwork.Exact H N NL) (ordinaryN : ∀e,N.edge e=Signature.equality)
variable (positive : 0<n) (u : Bool→L) (c : L) (nonzero : c≠0)
variable (form : N.denote=fun x=>c*Signature.unaryPower u n x)

def graph : Network AlgebraicComplex n := N.map L.subtype
def labels : Labelling (graph L N).shape r 1 b := NL
include exactN in
theorem exact : LabelledNetwork.Exact (C.ambient L H) (graph L N) (labels L N NL) := by
  intro v
  exact congrArg (RingHomRealization.mapAny L.subtype) (exactN v)
include ordinaryN in
theorem ordinary : ∀e,(graph L N).edge e=Signature.equality := by
  intro e
  funext p q
  change L.subtype (N.edge e p q)=Signature.equality p q
  rw [ordinaryN e]
  cases p <;> cases q <;> rfl
include form in
theorem value : (graph L N).denote=fun x=>(c : AlgebraicComplex)*Signature.unaryPower (fun b=>(u b : AlgebraicComplex)) n x := by
  funext x
  rw [graph,Network.denote_map,form]
  change L.subtype (c*Signature.unaryPower u n x)=_
  simp only [Signature.unaryPower,map_mul,map_prod]
  rfl

def toOriginal := Programme.compose
  (O.controlled (C.ambient L H) (graph L N) (labels L N NL) (exact L H N NL exactN)
    (ordinary L N ordinaryN) positive (fun b=>(u b : AlgebraicComplex)) (c : AlgebraicComplex)
    (by intro h;exact nonzero (Subtype.ext h)) (value L N u c form))
  (Programme.compose (C.controlled L F H) back)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPowerSource
end
