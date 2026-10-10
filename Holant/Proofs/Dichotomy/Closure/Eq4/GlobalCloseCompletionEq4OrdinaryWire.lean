import Holant.Complexity.EdgeSubdivision.Reduction
import Holant.Complexity.EdgeSubdivision.WireEquivalence
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentEvenCSPSource
import Holant.Proofs.Reductions.CanonicalFamily.Semantics

/-! Literal ordinary-edge access from a retained identity binary. Each old
edge becomes two native-X edges and one occurrence of that exact identity
label. Old vertex labels, port orders and coefficients remain unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4OrdinaryWire
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Choice
export UniversalPairReduction.Surgery.Choice (table evaluate denote_eq_evaluate)
end Choice
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (H : (i : Fin s) → Signature K (a i.val))
variable (j : Fin s) (literal : (⟨a j.val,H j⟩ : AnySignature K)=
  ⟨2,fun x => Signature.equality (x 0) (x 1)⟩)

abbrev ordinaryTables := QuaternaryOrdinaryCompanion.tables F H
abbrev nativeTables := GeneralFieldReduction.targetTables F H
abbrev extended := EdgeSubdivision.extendedSignatures H (fun _ : Fin 1 => Signature.equality)
abbrev extendedTables := GeneralFieldReduction.targetTables F (extended H)

def label (i : Fin (s+1)) : Fin s := if h : i.val<s then ⟨i.val,h⟩ else j

include literal in
theorem label_literal (i : Fin (s+1)) :
    (⟨a (label j i).val,H (label j i)⟩ : AnySignature K)=
      ⟨EdgeSubdivision.targetArity s a i.val,extended H i⟩ := by
  by_cases hi : i.val<s
  · have h := EdgeSubdivision.extendedSignatures_old_heq H
      (fun _ : Fin 1 => Signature.equality) ⟨i.val,hi⟩
    have hlabel : label j i=⟨i.val,hi⟩ := by simp [label,hi]
    rw [hlabel]
    exact (Sigma.ext (by simp [EdgeSubdivision.targetArity,hi]) h).symm
  · have he : i.val=s := by have := i.isLt; omega
    have hh : i=Fin.natAdd s (0 : Fin 1) := Fin.ext he
    rw [show label j i=j by simp [label,hi],literal,hh]
    exact (Sigma.ext (by simp [EdgeSubdivision.targetArity])
      (EdgeSubdivision.extendedSignatures_new_heq H
        (fun _ : Fin 1 => Signature.equality) (0 : Fin 1))).symm

include H literal in
theorem label_arity (i : Fin (s+1)) :
    a (label j i).val=EdgeSubdivision.targetArity s a i.val :=
  congrArg Sigma.fst (label_literal H j literal i)

def query := Relabel.input (label j) (label_arity H j literal)

private def read (f : AnySignature K) (bits : List Bool) := f.2 (fun i => bits.getD i.val false)

include literal in
theorem label_table (i : Fin (s+1)) (bits : List Bool) :
    Choice.table (extended H) i.val bits=Choice.table H (label j i).val bits := by
  have h := congrArg (fun f => read f bits) (label_literal H j literal i)
  simpa only [read,Choice.table,dif_pos i.isLt,dif_pos (label j i).isLt] using h.symm

theorem query_value (r : ExactSignatureTables.Input (s+1) 1 (EdgeSubdivision.targetArity s a)) :
    (nativeTables F H).evaluate F (query H j literal r)=(extendedTables F H).evaluate F r := by
  rw [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate,
    Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  have h := Relabel.value_scaled (label j) (Choice.table (extended H)) (Choice.table H)
    (fun _ => (1 : K)) (label_arity H j literal) r (fun i bits => by
      simpa using label_table H j literal i bits)
  have hp : Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
      (fun _ : Fin (s+1) => (1 : K)) r.val=1 := by
    unfold Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
    apply List.prod_eq_one
    intro z hz
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hz
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
    have hi := (r.property.1 i).1
    simp only [Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.total,
      dite_eq_left hi]
  rw [hp,one_mul] at h
  exact h.symm

def relabelControlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1 (EdgeSubdivision.targetArity s a)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((extendedTables F H).evaluate F) ((nativeTables F H).evaluate F) :=
  controlledOneQueryOfEq (Relabel.computes (label j) (label_arity H j literal))
    (identityComputes F.encoding) ((nativeTables F H).outputBound F)
    ((extendedTables F H).evaluate F) (fun r => (query_value F H j literal r).symm)

theorem subdivision_tables : EdgeSubdivision.targetTables (ordinaryTables F H)
    (fun (_ : Fin 1) b c => F.decode.symm (Signature.equality b c))
    (fun b c => F.decode.symm (Signature.disequality b c))=extendedTables F H := by
  unfold EdgeSubdivision.targetTables ordinaryTables QuaternaryOrdinaryCompanion.tables
    extendedTables GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  funext i x
  unfold extended EdgeSubdivision.extendedSignatures
  split <;> rfl

theorem fuse (j' : Fin 1) (b c : Bool) :
    (∑uv : Bool×Bool,
      F.decode (F.decode.symm (Signature.disequality b uv.1)) *
      F.decode (F.decode.symm (Signature.equality uv.1 uv.2)) *
      F.decode (F.decode.symm (Signature.disequality uv.2 c)))=
        F.decode ((ordinaryTables F H).edge j' b c) := by
  cases b <;> cases c <;>
    simp [ordinaryTables,QuaternaryOrdinaryCompanion.tables,Fintype.sum_prod_type,
      Fintype.sum_bool,Signature.equality,Signature.disequality]

def subdivideControlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (RawClosedNetwork.validatedEncoding (s+1) 1 (EdgeSubdivision.targetArity s a)) F.encoding
    ((ordinaryTables F H).evaluate F) ((extendedTables F H).evaluate F) := by
  apply controlledOneQueryOfEq (EdgeSubdivision.Compiler.computes s 1 a)
    (identityComputes F.encoding) ((extendedTables F H).outputBound F)
  intro r
  have h := EdgeSubdivision.evaluate_subdivision F (ordinaryTables F H)
    (fun (_ : Fin 1) b c => F.decode.symm (Signature.equality b c))
    (fun b c => F.decode.symm (Signature.disequality b c)) (fuse F H) r
  rw [subdivision_tables] at h
  exact h.symm

/-- Fixed-field ordinary Holant access uses one subdivision and one literal
label recoding, both with internally established valid query-byte control. -/
def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((ordinaryTables F H).evaluate F) ((nativeTables F H).evaluate F) :=
  Programme.compose (subdivideControlled F H) (relabelControlled F H j literal)

abbrev withX := EdgeSubdivision.extendedSignatures H (fun _ : Fin 1 => Signature.disequality)
abbrev withXTables := QuaternaryOrdinaryCompanion.tables F (withX H)

private theorem kernel_false : EdgeSubdivision.WirePath.kernel (K:=K) false=Signature.equality := by
  funext b c
  cases b <;> cases c <;> rfl

private theorem kernel_true : EdgeSubdivision.WirePath.kernel (K:=K) true=Signature.disequality := by
  funext b c
  cases b <;> cases c <;> rfl

theorem swap_source_tables : EdgeSubdivision.WireEquivalence.tables F (nativeTables F H).vertex
    true false=withXTables F H := by
  unfold EdgeSubdivision.WireEquivalence.tables EdgeSubdivision.WireEquivalence.kernelCoordinates
    nativeTables GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
    withXTables QuaternaryOrdinaryCompanion.tables withX
  simp only [kernel_false,kernel_true]
  congr 1
  funext i x
  unfold EdgeSubdivision.extendedSignatures
  split <;> rfl

theorem swap_target_tables : EdgeSubdivision.WireEquivalence.tables F (nativeTables F H).vertex
    false true=extendedTables F H := by
  unfold EdgeSubdivision.WireEquivalence.tables EdgeSubdivision.WireEquivalence.kernelCoordinates
    nativeTables extendedTables GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables extended
  simp only [kernel_false,kernel_true]
  congr 1
  funext i x
  unfold EdgeSubdivision.extendedSignatures
  split <;> rfl

/-- Include the literal X vertex in the ordinary source. This preserves the
mandatory native edge in a later common-basis test, not only the old rows. -/
def withXControlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1 (EdgeSubdivision.targetArity s a)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((withXTables F H).evaluate F) ((nativeTables F H).evaluate F) := by
  let W := EdgeSubdivision.WireEquivalence.tables F (nativeTables F H).vertex
  have step : LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) 1 (EdgeSubdivision.targetArity s a)) F.encoding
      (RawClosedNetwork.validatedEncoding (s+1) 1 (EdgeSubdivision.targetArity s a)) F.encoding
      ((W true false).evaluate F) ((W false true).evaluate F) := by
    apply controlledOneQueryOfEq (EdgeSubdivision.WireEquivalence.computes s a)
      (identityComputes F.encoding) ((W false true).outputBound F)
    intro r
    rw [EdgeSubdivision.WireEquivalence.evaluate_eq,EdgeSubdivision.WireEquivalence.evaluate_eq]
    exact (EdgeSubdivision.WireEquivalence.query_value
      (fun i x => F.decode ((nativeTables F H).vertex i x)) true false r).symm
  dsimp only [W] at step
  rw [swap_source_tables,swap_target_tables] at step
  exact Programme.compose step (relabelControlled F H j literal)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4OrdinaryWire
end
