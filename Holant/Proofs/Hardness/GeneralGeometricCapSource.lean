import Holant.Proofs.Hardness.GeneralGeometricCapPairAccess
import Holant.Proofs.Hardness.AdaptiveEOUnitSource
import Holant.Proofs.Algorithms.CBStandardNativeHardness
import Holant.Proofs.Counting.Hardness

/-! Original-M counting through actual unequal-norm binary caps. The literal
coefficient condition supplies the finite cap choice and internally proves
infinite geometric order. The physical interpolation answers use the original
field/presentation. This covers the adaptive four-required-entry EO scope,
not the universal EO dichotomy. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapSource
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
namespace Cost
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le configurationWord codedStoragePolynomial coded_storage_le)
end Cost
set_option backward.isDefEq.respectTransparency false


variable {L : Type} [NormedField L] [Algebra ℚ L]

def Applicable (M : Signature L 4) : Prop :=
  DenseEOUnitLocal.EOSupport M ∧ AdaptiveEOUnitLocal.NonzeroMiddle M ∧ GeneralGeometricCapLocal.Applicable M

variable (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (h : Applicable M)
local instance fieldAlgebra : Algebra ℚ (Original.field M) := (Original.field M).algebra'

theorem paired_value : AdaptiveEOUnitSource.value M halg=SparseOriginalPairAccess.pairValue M halg := rfl

def unitSource : LengthControlledOracleReduction SparseUnitValue.encoding (F M halg).encoding
    Original.targetEncoding (F M halg).encoding
    (SparseUnitValue.value (K:=Original.field M)) (Original.targetValue M halg) := by
  let first := AdaptiveEOUnitSource.source M halg h.1 h.2.1
  rw [paired_value] at first
  exact Compose.composeControlled first
    (GeneralGeometricCapPairAccess.source M halg (DenseEOUnitLocal.even M h.1) h.2.2)

variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    Original.targetEncoding (F M halg).encoding f (Original.targetValue M halg) :=
  Compose.composeControlled (Holant.LocalDrafts.MainChain.CBSpecializedNativeHardness.source (F M halg) w)
    (unitSource M halg h)

include h in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) := by
  intro α ea f w
  exact ⟨(source M halg h w).reduction⟩

def outputs (w : SharpPWitness ea f) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (x : α) : (source M halg h w).reduction.machine.OutputsInTime oracle (ea.encode x)
      (encodingNatBool.encode (f x)) ((source M halg h w).reduction.time.eval (ea.encode x).length) :=
  (source M halg h w).reduction.correct oracle ho x

theorem prefix_fees (w : SharpPWitness ea f) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (x : α) (t : ℕ) (ht : t≤(source M halg h w).reduction.time.eval (ea.encode x).length) :
    Cost.runFee (source M halg h w).reduction.machine oracle (ea.encode x) t≤
      (Cost.feePolynomial (source M halg h w)).eval (ea.encode x).length :=
  Cost.runFee_le (source M halg h w) oracle ho x t ht

theorem prefix_storage (w : SharpPWitness ea f) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Original.targetEncoding (F M halg).encoding (Original.targetValue M halg) oracle)
    (x : α) (t : ℕ) (ht : t≤(source M halg h w).reduction.time.eval (ea.encode x).length)
    (c : (source M halg h w).reduction.machine.Cfg)
    (hr : (source M halg h w).reduction.machine.run oracle (ea.encode x) t=some c) :
    (Cost.configurationWord (source M halg h w).reduction.machine c).length≤
      (Cost.codedStoragePolynomial (source M halg h w)).eval (ea.encode x).length :=
  Cost.coded_storage_le (source M halg h w) oracle ho x t ht c hr

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : CountingBridge.StandardMachine.Model Δ Q) (input : Bool→Δ)
variable (hinj : Function.Injective input) (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def physicalSource : LengthControlledOracleReduction ea encodingNatBool Original.targetEncoding (F M halg).encoding
    (m.physicalCount (CountingBridge.StandardMachine.InputRecoding.injectedEncoding ea input hinj))
    (Original.targetValue M halg) :=
  Compose.composeControlled
    (Holant.LocalDrafts.MainChain.CBStandardNativeHardness.source (ea:=ea) m input hinj clock htime (F M halg))
    (unitSource M halg h)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapSource
