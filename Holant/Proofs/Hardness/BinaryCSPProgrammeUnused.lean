import Holant.Proofs.Hardness.BinaryCSPProgrammeValidated
import Holant.Proofs.Hardness.EOBinaryPlaneRawValue

/-! Count unused declared variables by an actual variable-range/occurrence
scan. The same-field power programme supplies the exact missing factor two
per variable when the original-M/native-X graph has no row for that variable. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeUnused
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace R
export BinaryCSPProgrammeRecords (addresses addressesComputes)
end R
namespace S
export BinaryCSPProgrammeScan (occurrences occurrencesComputes positionsEncoding)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

theorem occurrences_eq_nil (xs : List ℕ) (v : ℕ) : S.occurrences xs v=[] ↔ v∉xs := by
  constructor
  · intro h hv
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
    have hm : i.val∈S.occurrences xs v := by
      simp only [S.occurrences,List.mem_filter,List.mem_range,decide_eq_true_eq]
      refine ⟨i.isLt,?_⟩
      rw [List.getD_eq_get xs 0 i,hi]
    rw [h] at hm
    exact List.not_mem_nil hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    obtain ⟨hi,he⟩ := List.mem_filter.mp hi
    have hlt := List.mem_range.mp hi
    have he' : xs.getD i 0=v := of_decide_eq_true he
    apply h
    rw [←he',List.getD_eq_get xs 0 ⟨i,hlt⟩]
    exact List.get_mem _ _

def unused (r : Raw) : ℕ :=
  ((List.range r.variables).filter (fun v => decide (v∉R.addresses r))).length

def unusedComputes : Computes encoding unary unused := by
  let source := pairEncoding encoding unary
  let r := Wiring.firstComputes encoding unary
  let v := Wiring.secondComputes encoding unary
  let occ := (pairComputes (r.andThen R.addressesComputes) (v.andThen UnaryBinary.computes)).andThen S.occurrencesComputes
  let test := (pairComputes occ (constantComputes source S.positionsEncoding [])).andThen
    (equalComputes S.positionsEncoding)
  let cell := ifComputes test (constantComputes source Frame.wordEncoding [true])
    (constantComputes source Frame.wordEncoding [])
  refine recode (BinaryInterpolation.WeightCompiler.rangeWordsComputes encoding Raw.variables
    variablesComputes (fun x => if S.occurrences (R.addresses x.1) x.2=[] then [true] else [])
    (congrComputes cell (fun _ => by simp))) id (fun _ => rfl) ?_
  intro r
  change (List.range r.variables).flatMap
    (fun v => if S.occurrences (R.addresses r) v=[] then [true] else [])=
      List.replicate (unused r) true
  simp only [occurrences_eq_nil,unused]
  induction List.range r.variables with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : v∈R.addresses r <;>
      simp only [List.flatMap_cons,List.filter_cons,h,not_true_eq_false,not_false_eq_true,
        decide_true,decide_false,ite_true,ite_false,List.nil_append,List.singleton_append,
        List.length_cons,List.replicate_succ,ih,Bool.false_eq_true]

theorem unused_eq (r : BinaryCSPProgrammeValidated.Input) :
    unused r.val=EOBinaryPlaneRawValue.unused r.val r.property := by
  rw [EOBinaryPlaneRawValue.unused_natural]
  unfold unused GeneralCSPUnusedNat.unused
  congr 1
  apply List.filter_congr
  intro v _
  simp [R.addresses,EOBinaryPlaneRaw.addresses]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeUnused
