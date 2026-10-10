import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralImplicationValue
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeBinaryThreeUnsignedSigned
import Holant.Proofs.Hardness.BinaryCSPCountingSource
import Holant.Proofs.Hardness.BinaryCSPProgrammeRestricted
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Closure.ProgrammeCompose

/-! Counts reduce to an actual unsigned weighted implication table. The
NAND-to-implication writer, sign-star interpolation and support interpolation
are all executed in the same original fixed-field presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralImplicationSource
open Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace U
export OrdinaryNegativeBinaryThreeUnsignedSigned (controlled sourceValue targetValue)
end U
namespace Q
export NoXGeneralImplicationQuery (query queryComputes)
export NoXGeneralImplicationValue (value)
end Q
namespace R
export BinaryCSPProgrammeRestricted (supportControlled sourceValue targetValue)
end R
namespace V
export BinaryCSPProgrammeValue (value weight)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (F : FixedField K d)

def signed : LengthControlledOracleReduction P.inputEncoding F.encoding P.inputEncoding F.encoding
    (BinaryCSPProgrammeSigned.sourceValue (K:=K)) (U.sourceValue (K:=K)) :=
  controlledOneQueryOfEq Q.queryComputes (identityComputes F.encoding)
    (U.controlled F).sourceOutputBound (BinaryCSPProgrammeSigned.sourceValue (K:=K))
    (fun r=>(Q.value r.val r.property).symm)

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}
def unweighted (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    P.inputEncoding F.encoding count (U.targetValue (K:=K)) :=
  Programme.compose (Programme.compose (BinaryCSPCountingSource.source F w) (signed F)) (U.controlled F)

local instance : DecidableEq K := Classical.decEq K
variable (f : Bool→Bool→K)
variable (h00 : f false false≠0) (h01 : f false true≠0) (h10 : f true false=0) (h11 : f true true≠0)

omit [Algebra ℚ K] in
include h00 h01 h10 h11 in
theorem indicator (x y : Bool) : (if f x y=0 then (0:K) else 1)=BinaryThreeSupportGates.implication x y := by
  classical
  cases x <;> cases y <;> simp [BinaryThreeSupportGates.implication,h00,h01,h10,h11]

omit [Algebra ℚ K] in
private theorem indicator_prod (xs : List K) :
    (if xs.prod=0 then (0:K) else 1)=(xs.map (fun x=>if x=0 then (0:K) else 1)).prod := by
  classical
  induction xs with
  | nil=>simp
  | cons x xs ih=>
      by_cases hx : x=0
      · simp [hx]
      · by_cases hs : xs.prod=0
        · simp [hx,hs,←ih]
        · simp [hx,hs,←ih,mul_ne_zero hx hs]

omit [Algebra ℚ K] in
include h00 h01 h10 h11 in
theorem support_eq (r : P.Input) : R.sourceValue f r=U.targetValue (K:=K) r := by
  classical
  change (∑x : Fin r.val.variables→Bool,if V.weight f r.val x=0 then (0:K) else 1)=
    V.value BinaryThreeSupportGates.implication r.val
  apply Finset.sum_congr rfl
  intro x _
  unfold BinaryCSPProgrammeValue.weight
  rw [indicator_prod]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro e _
  exact indicator f h00 h01 h10 h11 _ _

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    P.inputEncoding F.encoding count (R.targetValue f) := by
  let q:=R.supportControlled F (f false false) (f false true) (f true true) f
    h00 h01 h11 (by intro x y;cases x <;> cases y <;> simp [h10])
  have he : R.sourceValue f=U.targetValue (K:=K) := funext (support_eq f h00 h01 h10 h11)
  rw [he] at q
  exact Programme.compose (unweighted F w) q

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralImplicationSource
end
