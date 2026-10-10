import Holant.Proofs.Hardness.BinaryCSPProgrammeUnused
import Holant.Proofs.Hardness.BinaryCSPProgrammeValue
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction

/-! One original-signature/native-X query followed by the physically computed
unused-variable correction. Both oracle and corrected answers use exactly the
fixed original field presentation supplied at the theorem boundary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeNative
open Turing Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding query queryComputes)
end P
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (TargetInput targetEncoding)
end O
namespace U
export BinaryCSPProgrammeUnused (unused unusedComputes unused_eq)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (f : Bool→Bool→K)

def signature : Signature K 2 := fun x => f (x 0) (x 1)

def tables : ExactSignatureTables d 1 1 (fun _ => 4) where
  vertex _ x := F.decode.symm (M x)
  edge _ x y := F.decode.symm (Signature.disequality x y)

def targetValue : O.TargetInput→K := (tables F M).evaluate F
def sourceValue (r : P.Input) : K := BinaryCSPProgrammeValue.value f r.val

theorem target_semantics (q : O.TargetInput) : targetValue F M q=
    (q.val.realize q.property (fun _ => M) (fun _ => Signature.disequality)).denote Fin.elim0 := by
  simp only [targetValue,ExactSignatureTables.evaluate_eq_decoded,tables,LinearEquiv.apply_symm_apply]

theorem assignment_eq (r : Raw) (x : Fin r.variables→Bool) (i : ℕ) :
    BinaryCSPProgrammeValue.assignment r x i=EOBinaryPlaneRaw.read x i := by
  by_cases h : i<r.variables
  · rw [BinaryCSPProgrammeValue.assignment,List.getD_eq_getElem _ _ (by simpa using h)]
    simp [EOBinaryPlaneRaw.read,h]
  · rw [BinaryCSPProgrammeValue.assignment,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
    simp [EOBinaryPlaneRaw.read,h]

theorem value_eq (r : Raw) : BinaryCSPProgrammeValue.value f r=EOBinaryPlaneRaw.value (signature f) r := by
  unfold BinaryCSPProgrammeValue.value EOBinaryPlaneRaw.value
  apply Finset.sum_congr rfl
  intro x _
  unfold BinaryCSPProgrammeValue.weight
  congr 1
  apply List.map_congr_left
  intro e _
  simp [signature,assignment_eq]

theorem query_value (hm : M=EOBinaryPlaneCore.lift (signature f)) (r : P.Input) :
    sourceValue f r=targetValue F M (P.query r)*(2 : K)^U.unused r.val := by
  rw [sourceValue,value_eq,EOBinaryPlaneRawValue.query_value _ r.val r.property]
  rw [target_semantics,hm,U.unused_eq]
  exact mul_comm _ _

def unusedComputes : Computes P.inputEncoding unary (fun r => U.unused r.val) :=
  recode U.unusedComputes Subtype.val (fun _ => rfl) (fun _ => rfl)

def preprocessing (r : P.Input) : List O.TargetInput × ℕ := ([P.query r],U.unused r.val)
def pre : Computes P.inputEncoding (OracleBatch.contextEncoding O.targetEncoding unary) preprocessing :=
  pairComputes (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.list₁ O.targetEncoding P.queryComputes)
    unusedComputes

def post : Computes (OracleBatch.contextEncoding F.encoding unary) F.encoding
    (fun p : List K × ℕ => p.1.getD 0 0*(2 : K)^p.2) := by
  let power : Computes (pairEncoding F.encoding unary) F.encoding
      (fun p : K × ℕ => p.1*(2 : K)^p.2) :=
    congrComputes (ScalarPower.multiplyPower F (F.decode.symm (2 : K))) (fun _ => by simp)
  exact (pairComputes
    ((Wiring.firstComputes (framedListEncoding F.encoding) unary).andThen
      (FixedGadgetSubstitution.Compiler.getDComputes F.encoding 0 0))
    (Wiring.secondComputes (framedListEncoding F.encoding) unary)).andThen power

def controlled (hm : M=EOBinaryPlaneCore.lift (signature f)) :
    LengthControlledOracleReduction P.inputEncoding F.encoding O.targetEncoding F.encoding
      (sourceValue f) (targetValue F M) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch pre (post F)
    ((tables F M).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  rw [query_value F M f hm r]
  simpa only [preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero,targetValue] using
    reduction.reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeNative
