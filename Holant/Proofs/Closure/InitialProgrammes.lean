import Holant.Proofs.Closure.ProgrammeCompose
import Holant.Proofs.Closure.Interface

/-! Controlled reconstruction of the actual initial retained forest.
Every original local edge already has a controlled finite machine. This module
rebuilds their finite composition while retaining reachable-query guarantees.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.InitialProgrammes
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open FactorSaturation GeneralExtraction
open FrozenFactorNormalization

/-- Interpret the saved finite extraction chain with a controlled terminal.
This is an internal compositional lemma, not a caller-supplied final compiler. -/
def withTerminal {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {A : ℕ → ℕ}
    (F : FixedField K d) {G : (i : Fin s) → Signature K (A i.val)}
    {Q B : Type} {eq : Encoding Q Bool} {eb : Encoding B Bool} {g : Q → B}
    (base : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 A)
      F.encoding eq eb ((GeneralFieldReduction.targetTables F G).evaluate F) g)
    {n : ℕ} {H : (i : Fin n) → Signature K (A i.val)}
    (C : RecursiveMachine.Chain G H) :
    LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding n 1 A)
      F.encoding eq eb ((GeneralFieldReduction.targetTables F H).evaluate F) g :=
  match C with
  | .nil => base
  | .snoc previous f P => Programme.compose (RecursiveMachine.step F f P)
      (withTerminal F base previous)

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- The terminal ends at the original G encoding, including wire conversion. -/
def forestToOriginal : LengthControlledOracleReduction
    (WholeForest.inputEncoding (OriginalForestSource.roots G))
    (WholeForest.presentation (OriginalForestSource.roots G)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (WholeForest.sourceValue (OriginalForestSource.roots G)) (OriginalForestSource.value G) :=
  let D := OriginalForestSource.roots G
  withTerminal (WholeForest.presentation D)
    (Programme.compose (CommonField.originalTransport D.signature D.nonzero D.identity)
      (Programme.compose (OriginalCodec.transport D)
        (Programme.compose (RootPreprocessing.reverse (OriginalForestSource.nativeSignatures G)
          (OriginalForestSource.retains_identity G)) (OriginalWireTransport.nativeToLiteral G))))
    (WholeForest.chain D)

def toOriginal : LengthControlledOracleReduction
    (OriginalFrozenForest.OriginalInput.encoding G) (OI.presentation G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (OriginalLCodec.value (OI.publicTable G)) (OriginalForestSource.value G) :=
  let φ := OriginalFrozenForest.OriginalInput.embedding G
  let T := OriginalFrozenForest.OriginalInput.table G
  let hI := OriginalFrozenForest.OriginalInput.identity G
  Programme.compose (OriginalFrozenForest.publicToCoefficient φ T hI)
    (Programme.compose (OriginalFrozenForest.toCatalogue φ T hI)
      (Programme.compose (OriginalFrozenForest.catalogueToForest φ T hI) (forestToOriginal G)))

def fromOriginal : LengthControlledOracleReduction
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (OriginalFrozenForest.OriginalInput.encoding G) (OI.presentation G).encoding
    (OriginalForestSource.value G) (OriginalLCodec.value (OI.publicTable G)) :=
  let D := OriginalForestSource.roots G
  let φ := OriginalFrozenForest.OriginalInput.embedding G
  let T := OriginalFrozenForest.OriginalInput.table G
  let hI := OriginalFrozenForest.OriginalInput.identity G
  Programme.compose (OriginalWireTransport.literalToNative G)
    (Programme.compose (RootPreprocessing.controlled (OriginalForestSource.nativeSignatures G)
      (OriginalForestSource.retains_identity G))
      (Programme.compose (OriginalCodec.reverse D)
        (Programme.compose (OriginalFrozenForest.forestToCatalogue φ T hI)
          (Programme.compose (OriginalFrozenForest.fromCatalogue φ T hI)
            (OriginalFrozenForest.publicFromCoefficient φ T hI)))))

end Holant.LocalDrafts.RemoteWork.StableClosureV2.InitialProgrammes
