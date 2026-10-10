import Holant.Proofs.Hardness.BinaryCSPCountingSource
import Holant.Proofs.Hardness.BinaryCSPProgrammeRestricted
import Holant.Proofs.Closure.ProgrammeCompose

/-! An actual unsigned weighted-NAND CSP source in any supplied fixed field.
The support interpolation and signed-star programme are both executed; no
free negated-variable oracle is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDSource
open Holant Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
namespace C
export BinaryCSPProgrammeCore (Raw)
end C
namespace V
export BinaryCSPProgrammeValue (value weight assignment)
end V
namespace R
export BinaryCSPProgrammeRestricted (sourceValue targetValue supportControlled)
end R
namespace S
export BinaryCSPProgrammeSigned (sourceValue targetValue controlled)
end S
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
local instance : DecidableEq K := Classical.decEq K
variable (F : FixedField K d) (f : Bool → Bool → K)
variable (h00 : f false false ≠ 0) (h01 : f false true ≠ 0)
  (h10 : f true false ≠ 0) (h11 : f true true = 0)

include h00 h01 h10 h11 in
theorem indicator (x y : Bool) : (if f x y=0 then (0:K) else 1)=BinaryThreeSupportGates.nand x y := by
  classical
  cases x <;> cases y <;> simp [BinaryThreeSupportGates.nand,h00,h01,h10,h11]

private theorem indicator_prod (xs : List K) :
    (if xs.prod=0 then (0:K) else 1)=(xs.map (fun x=>if x=0 then (0:K) else 1)).prod := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x=0
    · simp [hx]
    · by_cases hs : xs.prod=0
      · simp [hx,hs,←ih]
      · simp [hx,hs,←ih,mul_ne_zero hx hs]

include h00 h01 h10 h11 in
theorem support_eq (r : P.Input) : R.sourceValue f r=S.targetValue (K:=K) r := by
  classical
  change (∑x : Fin r.val.variables→Bool,
    if V.weight f r.val x=0 then (0:K) else 1)=V.value BinaryThreeSupportGates.nand r.val
  apply Finset.sum_congr rfl
  intro x _
  unfold BinaryCSPProgrammeValue.weight
  rw [indicator_prod]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro e _
  exact indicator f h00 h01 h10 h11 _ _

def unsigned : LengthControlledOracleReduction P.inputEncoding F.encoding
    P.inputEncoding F.encoding (S.sourceValue (K:=K)) (R.targetValue f) := by
  let q := R.supportControlled F (f false false) (f false true) (f true false) f
    h00 h01 h10 (by intro x y; cases x <;> cases y <;> simp [h11])
  have eqv : R.sourceValue f=S.targetValue (K:=K) := funext (support_eq f h00 h01 h10 h11)
  rw [eqv] at q
  exact Programme.compose (S.controlled F) q

variable {α : Type} {ea : Encoding α Bool} {g : α → ℕ}
/-- Counts reduce to the literal unsigned weighted table, with its original
fixed-field answer codec and validated raw-CSP query codec. -/
def source (w : SharpPWitness ea g) : LengthControlledOracleReduction ea encodingNatBool
    P.inputEncoding F.encoding g (R.targetValue f) :=
  Programme.compose (BinaryCSPCountingSource.source F w) (unsigned F f h00 h01 h10 h11)
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDSource
end
