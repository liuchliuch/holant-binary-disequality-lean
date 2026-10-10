import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationProgramme
import Holant.Proofs.Reductions.CanonicalFamily.Semantics

/-! Literal source inclusion G+01 into [G,E]+01 over the same fixed field.
Only the appended pin label moves, from s to s+1. Every original ordered port,
edge, vertex occurrence and coefficient remains unchanged. The intervening E
label is never used by the inclusion and requires no semantic assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinDEQInclusion
open Computability Holant Holant.Complexity Holant.Algebraic
open BinaryCompose UniversalPairReduction
namespace P
export GeneralEOSinglePinAmplificationProgramme (sourceValue)
end P
namespace S
export GeneralEOSinglePinAmplificationSemantics (value)
end S
namespace A
export GeneralEOSinglePinAmplificationAccess (tables tables_value)
end A
namespace R
export Holant.LocalDrafts.Hardness.CanonicalFamily.Relabel
  (input computes raw row label vertices_length ordered_ports edges)
end R
namespace Choice
export UniversalPairReduction.Surgery.Choice (table evaluate weight rowValue denote_eq_evaluate)
end Choice
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K]
variable {d s : ℕ} {a b : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (H : (i : Fin (s+1)) → Signature K (b i.val))

def old (i : Fin s) : Fin (s+1) := i.castSucc

def label (i : Fin (s+1)) : Fin ((s+1)+1) :=
  if hi : i.val<s then ⟨i.val,by omega⟩ else ⟨s+1,by omega⟩

variable (hold : ∀i : Fin s,(⟨b i.val,H (old i)⟩ : AnySignature K)=
  ⟨a i.val,ValueJoins.signatures F T i⟩)

include hold in
theorem arity (i : Fin (s+1)) :
    extendedArity (s+1) b (label i).val=extendedArity s a i.val := by
  by_cases hi : i.val<s
  · have ha := congrArg Sigma.fst (hold ⟨i.val,hi⟩)
    simpa [label,hi,extendedArity,show i.val<s+1 by omega] using ha
  · simp [label,hi,extendedArity]

abbrev Input := ExactSignatureTables.Input (s+1) 1 (extendedArity s a)
abbrev TargetInput := ExactSignatureTables.Input ((s+1)+1) 1 (extendedArity (s+1) b)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (extendedArity s a)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding ((s+1)+1) 1 (extendedArity (s+1) b)

def query : Input (s:=s) (a:=a) → TargetInput (s:=s) (b:=b) :=
  R.input label (arity F T H hold)

def queryComputes : Computes (inputEncoding (s:=s) (a:=a)) (targetEncoding (s:=s) (b:=b))
    (query F T H hold) := R.computes label (arity F T H hold)

private def read (bits : List Bool) (z : AnySignature K) : K :=
  z.2 (fun i => bits.getD i.val false)

include hold in
theorem old_table (i : Fin s) (bits : List Bool) :
    Choice.table H i.val bits=Choice.table (ValueJoins.signatures F T) i.val bits := by
  unfold Choice.table
  rw [dif_pos i.isLt,dif_pos (show i.val<s+1 by omega)]
  exact congrArg (read bits) (hold i)

include hold in
theorem table_eq (i : Fin (s+1)) (bits : List Bool) :
    Choice.table (BinaryFamily.signatures (ValueJoins.signatures F T) BinaryTable.delta) i.val bits=
      Choice.table (BinaryFamily.signatures H BinaryTable.delta) (label i).val bits := by
  by_cases hi : i.val<s
  · have hl : (label i).val=i.val := by simp [label,hi]
    rw [hl,BinaryFamily.table_old _ _ i.val hi,
      BinaryFamily.table_old _ _ i.val (show i.val<s+1 by omega)]
    exact (old_table F T H hold ⟨i.val,hi⟩ bits).symm
  · have he : i.val=s := by omega
    have hl : (label i).val=s+1 := by simp [label,hi]
    rw [he,hl,BinaryFamily.table_new,BinaryFamily.table_new]

include hold in
theorem value_exact (r : Input (s:=s) (a:=a)) :
    P.sourceValue F T r=S.value H (query F T H hold r) := by
  change S.value (ValueJoins.signatures F T) r=S.value H (query F T H hold r)
  unfold S.value
  rw [Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  change Choice.evaluate (Choice.table (BinaryFamily.signatures (ValueJoins.signatures F T) BinaryTable.delta))
      r.val.edges.length r.val.vertices=
    Choice.evaluate (Choice.table (BinaryFamily.signatures H BinaryTable.delta))
      r.val.edges.length (r.val.vertices.map (R.row label))
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro z _
  unfold Choice.weight
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  have hi := (GeneralEOSinglePinAmplificationValidation.source_row r.property v hv).1
  change Choice.table _ v.1 (v.2.map (UniversalPairReduction.Surgery.Choice.bit _))=
    Choice.table _ (R.label label v.1) (v.2.map (UniversalPairReduction.Surgery.Choice.bit _))
  rw [R.label,dif_pos hi]
  exact table_eq F T H hold ⟨v.1,hi⟩ _

def targetOutput : PolynomialOutputBound (targetEncoding (s:=s) (b:=b)) F.encoding (S.value H) where
  bound := ((A.tables F H).outputBound F).bound
  length_le r := by
    have h := ((A.tables F H).outputBound F).length_le r
    rw [A.tables_value] at h
    exact h

/-- Actual validated one-query inclusion, with the answer encoded by F on both
ends. Its target is the full [G,E]+01 partition function accepted by the generic
amplifier, and no target evaluator or time bound is supplied. -/
def source : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a)) F.encoding
    (targetEncoding (s:=s) (b:=b)) F.encoding (P.sourceValue F T) (S.value H) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes F T H hold)
    (identityComputes F.encoding) (targetOutput F H) (P.sourceValue F T) (value_exact F T H hold)

theorem query_counts (r : Input (s:=s) (a:=a)) :
    (query F T H hold r).val.vertices.length=r.val.vertices.length ∧
    (query F T H hold r).val.edges=r.val.edges ∧
    (query F T H hold r).val.vertices.map Prod.snd=r.val.vertices.map Prod.snd :=
  ⟨R.vertices_length label r.val,rfl,R.ordered_ports label r.val⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinDEQInclusion
