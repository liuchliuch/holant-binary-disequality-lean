import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryChartSource
import Holant.Proofs.Dichotomy.Closure.Weighted.GlobalCloseCompletionWeightedEq4Source

/-! A genuine higher two-sided endpoint graph in the nonisotropic unary
chart gives an unconditional ordinary Eq4/two-pin source. The graph's actual
norm factors, original field and implemented old-family source are retained.
No period, inverse-weight gate or equality anchor is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryEndpointSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace U
export GeneralOddNonisotropicFrame (norm chart)
end U
namespace C
export GlobalCloseCompletionUnaryChartSource (chartTable graph labels exact graph_endpoint controlled)
end C
namespace Q
export GlobalCloseCompletionUnaryOrdinaryEquality (endpoint joined joinLabels joined_exact joined_ordinary joined_denote)
end Q
namespace W
export GlobalCloseCompletionWeightedEq4Normalization (Input)
export GlobalCloseCompletionWeightedEq4Source (data old_included obstruction)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r k degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (u : Signature L 1) (hu : U.norm u≠0)
variable (N : Network L (k+2)) (NL : Labelling N.shape r 1 b)
variable (hE : LabelledNetwork.Exact H N NL) (hO : ∀e,N.edge e=Signature.equality) (hk : 0<k)
variable (A B : L) (hA : A≠0) (hB : B≠0) (endpoint : U.chart u N.denote=Q.endpoint (k+2) A B)

/-- The two-copy graph is built in the actual chart table. Its endpoint
weights include norm(u) once per original internal edge, before squaring. -/
def weighted : W.Input G where
  K := L
  degree := degree
  F := F
  count := r
  b := b
  H := C.chartTable H u
  graph := Q.joined (C.graph u N)
  labels := Q.joinLabels (C.graph u N) (C.labels u N NL)
  exact := Q.joined_exact (C.chartTable H u) (C.graph u N) (C.labels u N NL) (C.exact H u N NL hE)
  ordinary := Q.joined_ordinary (C.graph u N) (fun _=>rfl)
  left := (U.norm u^N.shape.edges*A)^2
  right := (U.norm u^N.shape.edges*B)^2
  left_nonzero := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hu) hA)
  right_nonzero := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hu) hB)
  denote := Q.joined_denote (C.graph u N) hk _ _ (C.graph_endpoint u hu N hO A B endpoint)
  toOriginal := Programme.compose (C.controlled F H u hu) back

def data : GenericOrdinarySource.Data G :=
  W.data G (weighted G L F H back u hu N NL hE hO hk A B hA hB endpoint)

def chartedFamily : SignatureFamily AlgebraicComplex := Set.range fun i : Fin r=>
  RingHomRealization.mapAny L.subtype (⟨b i.val,C.chartTable H u i⟩ : AnySignature L)

theorem charted_included : chartedFamily L H u⊆
    GenericOrdinarySource.family G (data G L F H back u hu N NL hE hO hk A B hA hB endpoint) :=
  W.old_included G (weighted G L F H back u hu N NL hE hO hk A B hA hB endpoint)

theorem obstruction (negative : ¬Tract (chartedFamily L H u)) :
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess
      (GenericOrdinarySource.family G (data G L F H back u hu N NL hE hO hk A B hA hB endpoint))) :=
  W.obstruction G (weighted G L F H back u hu N NL hE hO hk A B hA hB endpoint) negative


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryEndpointSource
end
