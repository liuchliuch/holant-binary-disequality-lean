import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralImplicationSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralBinarySymmetry

/-! Every literal three-supported binary has a counted-verifier unsigned CSP
source. The four zero positions use real implication/NAND programmes, an edge
reversal, or one global assignment-complement bijection. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralThreeSupportSource
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace R
export BinaryCSPProgrammeRestricted (targetValue)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (F : FixedField K d) (f : Bool→Bool→K)
variable (hole : Bool×Bool) (zero : f hole.1 hole.2=0)
variable (live : ∀x y,(x,y)≠hole→f x y≠0)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    P.inputEncoding F.encoding count (R.targetValue f) := by
  rcases hole with ⟨h,k⟩
  cases h <;> cases k
  · exact Programme.compose
      (OrdinaryNegativeNANDSource.source F (fun x y=>f (!x) (!y))
        (live true true (by decide)) (live true false (by decide))
        (live false true (by decide)) zero w)
      (NoXGeneralBinarySymmetry.flip F f)
  · exact Programme.compose
      (NoXGeneralImplicationSource.source F (fun x y=>f y x)
        (live false false (by decide)) (live true false (by decide)) zero
        (live true true (by decide)) w)
      (NoXGeneralBinarySymmetry.transpose F f)
  · exact NoXGeneralImplicationSource.source F f
      (live false false (by decide)) (live false true (by decide)) zero
      (live true true (by decide)) w
  · exact OrdinaryNegativeNANDSource.source F f
      (live false false (by decide)) (live false true (by decide))
      (live true false (by decide)) zero w

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralThreeSupportSource
end
