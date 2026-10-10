import Holant.Proofs.Hardness.GeneralEOPairedCSPValidated
import Holant.Proofs.Hardness.BinaryCSPProgrammeUnused

/-! Actual unused-variable counter for arbitrary-arity CSP input. Variable
names are binary words; only declared unary input counts bound all scans. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPUnused
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GeneralEOPairedCSPRaw FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace S
export BinaryCSPProgrammeScan (occurrences occurrencesComputes positionsEncoding)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

def unused (r : Raw) : ℕ :=
  ((List.range r.variables).filter (fun v => decide (v∉r.addresses))).length

def unusedComputes : Computes encoding unary unused := by
  let source := pairEncoding encoding unary
  let r := Wiring.firstComputes encoding unary
  let v := Wiring.secondComputes encoding unary
  let occ := (pairComputes (r.andThen addressesComputes) (v.andThen UnaryBinary.computes)).andThen S.occurrencesComputes
  let test := (pairComputes occ (constantComputes source S.positionsEncoding [])).andThen
    (equalComputes S.positionsEncoding)
  let cell := ifComputes test (constantComputes source Frame.wordEncoding [true])
    (constantComputes source Frame.wordEncoding [])
  refine recode (BinaryInterpolation.WeightCompiler.rangeWordsComputes encoding Raw.variables
    variablesComputes (fun x => if S.occurrences (x.1.addresses) x.2=[] then [true] else [])
    (congrComputes cell (fun _ => by simp))) id (fun _ => rfl) ?_
  intro r
  change (List.range r.variables).flatMap
    (fun v => if S.occurrences (r.addresses) v=[] then [true] else [])=
      List.replicate (unused r) true
  simp only [BinaryCSPProgrammeUnused.occurrences_eq_nil,unused]
  induction List.range r.variables with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : v∈r.addresses <;>
      simp only [List.flatMap_cons,List.filter_cons,h,not_true_eq_false,not_false_eq_true,
        decide_true,decide_false,ite_true,ite_false,List.nil_append,List.singleton_append,
        List.length_cons,List.replicate_succ,ih,Bool.false_eq_true]

theorem unused_eq {n : ℕ} (p : OrientedPerfectPairing n) (r : Input p.count) :
    unused r.val=GeneralCSPUnused.unusedCount (scope p r.val r.property) := by
  rw [GeneralEOPairedCSPScan.NatScan.unusedCount_filter,addresses_scope]
  unfold unused GeneralEOPairedCSPScan.NatScan.unused GeneralCSPUnusedNat.unused
  congr 1
  apply List.filter_congr
  intro v _
  simp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPUnused
