import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2QuaternaryCurrent
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2PrimeCharts
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins

/-! Strong actual current-C2 prime q4 source: a real Eq4 graph for the whole
ordinary dictionary, or a genuine whole-family tractable/hard conclusion.
There is no Affine selected-row residual in this interface. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PrimeCurrent
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Certificates.EqualityQuaternary
namespace S
export GlobalCloseCompletionStopOrdinarySource (field table family presentation toOriginal)
end S
namespace C
export GlobalCloseCompletionC2QuaternaryCurrent (values algebraic_tensor source_row source_z)
end C
namespace E
export GlobalCloseCompletionC2OrdinaryPairOutcome (HasEq4)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (S.field G P) := (S.field G P).algebra'
variable (torsion : ResidualTorsion P.family) (hI : RetainsIdentity P.family)
variable (cardTwo : Nat.card (completeGroup P.family torsion)=2)
variable (f : Signature (OI.K G) 4) (retained : (⟨4,f⟩ : AnySignature (OI.K G))∈P.family)
variable (prime : Prime (⟨4,f⟩ : AnySignature (OI.K G)))
variable (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)

include torsion hI cardTwo retained prime stable in
theorem classified : E.HasEq4 (S.table G P) ∨ Tract (S.family G P) ∨ NoXWeightedAntiSquares.Hard G := by
  let g := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f
  let v := C.values g
  let phi : OI.K G→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp (ClosureSourceRows.embedding G)
  have accepted : GlobalCloseCompletionC2Q4Union.Accepted (fun i=>(v i:ℂ)) :=
    GlobalCloseCompletionC2Q4Closed.current_accepted P.family torsion hI cardTwo phi f stable
  have comp : ∀x,g x=g (fun i=>!(x i)) := fun x=>congrArg (ClosureSourceRows.embedding G)
    (GlobalCloseCompletionC2CurrentComplement.current_complement P.family torsion hI cardTwo f stable x)
  obtain ⟨N,equation⟩ := C.source_row G P f retained
  obtain ⟨z,zLiteral⟩ := C.source_z G P
  have form : RingHomRealization.mapSignature (S.field G P).subtype N.network.denote=
      sourceKBasis.action (GlobalCloseCompletionC2Q4UnionCurrent.tensor v) := by
    rw [C.algebraic_tensor g comp]
    exact equation
  have mappedPrime : Prime (⟨4,g⟩ : AnySignature AlgebraicComplex) :=
    (prime_mapSignature_iff (ClosureSourceRows.embedding G) (⟨4,f⟩ : AnySignature (OI.K G))).mpr prime
  have tensorPrime := prime_coordinateAction ((PrimalityInterfaces.retained_equality_prime g).mp mappedPrime)
    (fun _=>sourceKBasis.matrix) (fun _=>sourceKBasis.inverse) (fun _=>sourceKBasis.inverse_matrix)
  have originalPrime : Prime (⟨4,N.network.denote⟩ : AnySignature (S.field G P)) := by
    apply (prime_mapSignature_iff (S.field G P).subtype (⟨4,N.network.denote⟩ : AnySignature (S.field G P))).mp
    apply (PrimalityInterfaces.retained_equality_prime _).mpr
    change TensorPrime (RingHomRealization.mapSignature (S.field G P).subtype N.network.denote)
    rw [equation]
    exact tensorPrime
  exact GlobalCloseCompletionC2PrimeCharts.classified G (S.field G P) (S.presentation G P)
    (S.table G P) (S.toOriginal G P) z zLiteral N v form accepted originalPrime

variable (hasEq4 : E.HasEq4 (S.table G P))

def anchor : GlobalCloseCompletionOrdinaryAnchorInput.Input G :=
  let N := hasEq4.choose
  let c := hasEq4.choose_spec.choose
  { K := S.field G P
    degree := Module.finrank ℚ (S.field G P)
    F := S.presentation G P
    count := P.count
    b := P.arity
    H := S.table G P
    graph := N.network
    labels := N.labels
    exact := N.exact
    ordinary := N.edges
    scalar := c
    nonzero := hasEq4.choose_spec.choose_spec.1
    denote := hasEq4.choose_spec.choose_spec.2
    toOriginal := S.toOriginal G P }

def data : GenericOrdinarySource.Data G := GlobalCloseCompletionOrdinaryAnchorPins.data G (anchor G P hasEq4)

theorem old_included : S.family G P⊆GenericOrdinarySource.family G (data G P hasEq4) :=
  GlobalCloseCompletionOrdinaryAnchorPins.old_included G (anchor G P hasEq4)

theorem z_member : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈GenericOrdinarySource.family G (data G P hasEq4) :=
  old_included G P hasEq4 (GlobalCloseCompletionStopOrdinarySource.z_member G P)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PrimeCurrent
end
