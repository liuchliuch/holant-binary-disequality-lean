import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTraceOrX
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsChartPullback
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryFramedSelector
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroPins
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsIsotropic

/-! A stable sourced boundary for the genuine unary terminal consumers.
Every nonzero actual unary, retained Z and whole-family negative guard is
consumed internally to a sourced ternary prime, sourced nonsingular paired
quaternary, or sourced literal two-pin table. No endpoint callback and no
independent-pair hardness assertion occurs in the producer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryStructuralSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Q
export GlobalCloseCompletionUnaryQuaternaryForm (Paired determinant)
end Q
namespace D
export GlobalCloseCompletionUnaryDescentSource (ambient)
end D
namespace C
export GlobalCloseCompletionUnaryFramedSelector
  (table pin scale scale_nonzero pin0 pin1 obstruction source result)
end C
namespace Z
export GlobalCloseCompletionUnaryZeroPins (data obstruction)
end Z
namespace I
export GlobalCloseCompletionIndependentPinsIsotropic (data obstruction hasX)
export GlobalCloseCompletionUnaryIsotropicLift (zLabel z_literal)
end I
namespace S
export GlobalCloseCompletionIndependentPinsSource (Data family)
end S
namespace U
export GeneralOddNonisotropicFrame (norm)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure PinSource : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K:=K.algebra';FixedField K degree
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature K (arity i.val)
  originalTable : (i : Fin count)→Signature K (arity i.val)
  originalFirst : NoXOrdinaryGraphAdjoin.Output originalTable 1
  originalNorm : U.norm originalFirst.network.denote≠0
  originalZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈D.ambient K originalTable
  originalNegative : ¬Tract (D.ambient K originalTable)
  originalToOriginal : letI : Algebra ℚ K:=K.algebra';LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F originalTable).evaluate F) (OriginalForestSource.value G)
  chart_eq : table=GlobalCloseCompletionUnaryChartSource.chartTable originalTable originalFirst.network.denote
  first : NoXOrdinaryGraphAdjoin.Output table 1
  scalar : K
  nonzero : scalar≠0
  pin0 : first.network.denote (fun _=>false)=scalar
  pin1 : first.network.denote (fun _=>true)=0
  negative : ¬Tract (D.ambient K table)
  toOriginal : letI : Algebra ℚ K:=K.algebra';LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F table).evaluate F) (OriginalForestSource.value G)

structure TernarySource : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K:=K.algebra';FixedField K degree
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature K (arity i.val)
  hasZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈D.ambient K table
  negative : ¬Tract (D.ambient K table)
  toOriginal : letI : Algebra ℚ K:=K.algebra';LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F table).evaluate F) (OriginalForestSource.value G)
  graph : NoXOrdinaryGraphAdjoin.Output table 3
  prime : Prime (⟨3,graph.network.denote⟩ : AnySignature K)
  chartedSource : PinSource G
  chartedGraph : NoXOrdinaryGraphAdjoin.Output chartedSource.table 3
  chartedPrime : Prime (⟨3,chartedGraph.network.denote⟩ : AnySignature chartedSource.K)

inductive Completion : Type 1 where
  | ternary (source : TernarySource G)
  | paired (source : PinSource G) (graph : NoXOrdinaryGraphAdjoin.Output source.table 4)
      (support : Q.Paired graph.network.denote) (nonsingular : Q.determinant graph.network.denote≠0)
  | pins (source : S.Data G) (negative : ¬Tract (S.family G source))
      (resource : GlobalCloseCompletionUnaryTraceOrX.Witness (S.family G source))

def PinSource.resource (src : PinSource G) :
    GlobalCloseCompletionUnaryTraceOrX.Witness (D.ambient src.K src.table) := by
  letI : Algebra ℚ src.K:=src.K.algebra'
  rw [src.chart_eq]
  exact GlobalCloseCompletionUnaryTraceOrX.chartWitness src.K src.originalTable
    src.originalFirst.network.denote src.originalNorm src.originalZ

def castOutput {K : Type} [Field K] {r n : ℕ} {b : ℕ→ℕ}
    {H J : (i : Fin r)→Signature K (b i.val)} (eqn : H=J) (N : NoXOrdinaryGraphAdjoin.Output H n) :
    NoXOrdinaryGraphAdjoin.Output J n := eqn ▸N

theorem castOutput_value {K : Type} [Field K] {r n : ℕ} {b : ℕ→ℕ}
    {H J : (i : Fin r)→Signature K (b i.val)} (eqn : H=J) (N : NoXOrdinaryGraphAdjoin.Output H n) :
    (castOutput eqn N).network.denote=N.network.denote := by cases eqn;rfl

def consume (src : PinSource G) (result : GlobalCloseCompletionUnaryUniversalSelector.Produced src.table) :
    Completion G := by
  letI : Algebra ℚ src.K:=src.K.algebra'
  cases result with
  | ternary N prime=>
    let M:=castOutput src.chart_eq N
    have hp : Prime (⟨3,M.network.denote⟩ : AnySignature src.K) := by
      rw [show M.network.denote=N.network.denote from castOutput_value src.chart_eq N]
      exact prime
    exact .ternary {
      K:=src.K,degree:=src.degree,F:=src.F,count:=src.count,arity:=src.arity
      table:=src.originalTable,hasZ:=src.originalZ,negative:=src.originalNegative
      toOriginal:=src.originalToOriginal
      graph:=GlobalCloseCompletionIndependentPinsChartPullback.output src.K src.originalTable
        src.originalFirst.network.denote M
      prime:=GlobalCloseCompletionIndependentPinsChartPullback.prime src.K src.originalTable
        src.originalFirst.network.denote M src.originalNorm hp
      chartedSource:=src,chartedGraph:=N,chartedPrime:=prime }
  | paired N support det=>exact .paired src N support det
  | zeroOrigin N positive nonzero zero=>
    exact .pins (Z.data G src.K src.F src.table src.toOriginal src.first src.scalar src.nonzero
      src.pin0 src.pin1 N nonzero zero)
      (Z.obstruction G src.K src.F src.table src.toOriginal src.first src.scalar src.nonzero
        src.pin0 src.pin1 N nonzero zero src.negative)
      ((PinSource.resource G src).mono (GlobalCloseCompletionUnaryZeroPins.old_included
        src.K src.F src.table src.first src.scalar))

section Source
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (first : NoXOrdinaryGraphAdjoin.Output H 1)
variable (negative : ¬Tract (D.ambient L H))
variable (normNonzero : U.norm first.network.denote≠0)

def framed (hasZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈D.ambient L H) : PinSource G where
  K:=L
  degree:=degree
  F:=F
  count:=r
  arity:=b
  table:=C.table L H first
  originalTable:=H
  originalFirst:=first
  originalNorm:=normNonzero
  originalZ:=hasZ
  originalNegative:=negative
  originalToOriginal:=back
  chart_eq:=rfl
  first:=C.pin L H first
  scalar:=C.scale L H first
  nonzero:=C.scale_nonzero L H first normNonzero
  pin0:=C.pin0 L H first normNonzero
  pin1:=C.pin1 L H first normNonzero
  negative:=C.obstruction L H first normNonzero negative
  toOriginal:=C.source L F H first normNonzero G back

def nonisotropic (hasZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈D.ambient L H) : Completion G :=
  consume G (framed G L F H back first negative normNonzero hasZ)
    (C.result L H first normNonzero negative)

variable (firstNonzero : first.network.denote≠0)
variable (hasZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈D.ambient L H)

def unary : Completion G := by
  classical
  by_cases hu : U.norm first.network.denote≠0
  · exact nonisotropic G L F H back first negative hu hasZ
  · have isotropic : U.norm first.network.denote=0:=not_not.mp hu
    let z:=I.zLabel L H hasZ
    have hz:=I.z_literal L H hasZ
    exact .pins (I.data L F H first firstNonzero isotropic z hz G back)
      (I.obstruction L F H first firstNonzero isotropic z hz G back negative)
      (.x (I.hasX L F H first firstNonzero isotropic z hz G back))


end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryStructuralSource
end
