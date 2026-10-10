import Holant.Proofs.Hardness.EOBinaryPlanePositiveSource
import Holant.Proofs.Hardness.BinaryCSPCountingSource
import Holant.Proofs.CountingMachines.StandardMachine.Source
import Holant.Proofs.Counting.Hardness

/-! Natural and conventional accepting-path counting into a positive binary
plane's original quaternary lift. Positivity and the actual complex coefficient
images are the only table hypotheses; all Ising and count programmes are built. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositiveCounting
open Holant Holant.Algebraic Holant.Complexity Computability
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace S
export EOBinaryPlanePositiveSource (controlled)
end S
namespace N
export BinaryCSPProgrammeNative (targetValue)
end N
namespace Q
export ExactTwoChainQueries (targetEncoding)
end Q
namespace Standard
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine (Model)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Source (standard_to_witness)
export Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputRecoding (injectedEncoding)
end Standard
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (f : Signature K 2) (into : K→+*ℂ) (g : Signature ℝ 2)
variable (hg : EOBinaryPlanePositive.Good g) (hi : ∀z,into (f z)=(g z : ℂ))
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    Q.targetEncoding F.encoding count (N.targetValue F (EOBinaryPlaneCore.lift f)) :=
  C.composeControlled
    (C.composeControlled (BinaryCSPCountingSource.source F w) (BinaryCSPProgrammeSigned.controlled F))
    (S.controlled F f into g hg hi)

include hg hi in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    Q.targetEncoding F.encoding (N.targetValue F (EOBinaryPlaneCore.lift f)) := by
  intro α ea count w
  exact ⟨(source F f into g hg hi w).reduction⟩

variable {Δ T : Type} [Fintype Δ] [Fintype T]
variable (m : Standard.Model Δ T) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool Q.targetEncoding F.encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj))
      (N.targetValue F (EOBinaryPlaneCore.lift f)) :=
  source F f into g hg hi (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositiveCounting
