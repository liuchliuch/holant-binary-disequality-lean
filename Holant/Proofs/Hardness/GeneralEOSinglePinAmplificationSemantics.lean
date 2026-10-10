import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationEvaluation
import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationCompiler
import Holant.Complexity.UniversalPairReduction.BinaryFamily
import Holant.Complexity.BinaryInterpolation.Chains.Template

/-! Semantic join from the actual anchored raw graph to the literal full
original-family plus directed-01 partition function. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationSemantics
open Holant Holant.Complexity FixedGadgetSubstitution UniversalPairReduction
namespace A
export GeneralEOSinglePinAmplificationCompiler (Input inputEncoding query queryComputes)
end A
namespace E
export GeneralEOSinglePinAmplificationEvaluation (sourceTable value)
end E
namespace Choice
export UniversalPairReduction.Surgery.Choice (table weight evaluate rowValue denote_eq_evaluate)
end Choice
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))

def value (r : A.Input (s:=s) (a:=a)) : K :=
  (r.val.realize r.property (BinaryFamily.signatures G BinaryTable.delta)
    (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0

theorem table_eq (label : ℕ) (hl : label<s+1) (bits : List Bool) :
    Choice.table (BinaryFamily.signatures G BinaryTable.delta) label bits=
      E.sourceTable s (Choice.table G) label bits := by
  by_cases h : label<s
  · rw [BinaryFamily.table_old G BinaryTable.delta label h]
    simp only [E.sourceTable,if_pos h]
  · have he : label=s := by omega
    subst label
    rw [BinaryFamily.table_new]
    simp [E.sourceTable,BinaryTable.delta,ExactTwoReferenceColours.pinValue]

theorem value_evaluate (r : A.Input (s:=s) (a:=a)) :
    value G r=Choice.evaluate (E.sourceTable s (Choice.table G)) r.val.edges.length r.val.vertices := by
  rw [value,Choice.denote_eq_evaluate]
  apply Finset.sum_congr rfl
  intro c _
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro v hv
  unfold Choice.rowValue
  exact table_eq G v.1 (GeneralEOSinglePinAmplificationValidation.source_row r.property v hv).1 _

variable (j : Fin s)
variable (hE : (⟨a j.val,G j⟩ : AnySignature K)=⟨4,ExactTwoSignatures.E⟩)

include hE in
theorem original_table (bits : List Bool) :
    Choice.table G j.val bits=ExactTwoSignatures.E (ExactTwoReferenceEvaluation.read4 bits) := by
  unfold Choice.table
  rw [dif_pos j.isLt]
  have h := BinaryInterpolation.Chains.signature_cast_apply (G j) ExactTwoSignatures.E hE
    (congrArg Sigma.fst hE) (ExactTwoReferenceEvaluation.read4 bits)
  exact h

abbrev query := A.query j.isLt (congrArg Sigma.fst hE)

include hE in
theorem query_value (r : A.Input (s:=s) (a:=a)) :
    BinaryFamily.value G BinaryTable.delta (query G j hE r)=value G r := by
  change value G (forget s a (query G j hE r))=value G r
  rw [value_evaluate,value_evaluate]
  exact E.value r.property (Choice.table G) j.isLt (original_table G j hE)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationSemantics
