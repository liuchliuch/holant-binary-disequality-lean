import Holant.Proofs.Hardness.GeneralCancellationCapPin
import Holant.Proofs.Hardness.SparseOriginalPairAccess
import Holant.Proofs.Reductions.ControlledCap

/-! All-occurrence [M,01] elimination for the finite union of twelve oriented
original-M cancellation caps. The literal coefficient predicate chooses the cap
internally. Original.field M, its presentation and target answer bytes remain
unchanged. The same physical compiler counts every original pin occurrence. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPairAccess
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
namespace Base
export SparseOriginalPairAccess (pairArity pairEncoding pairSignatures pairValue dictionary PairInput)
end Base
namespace DP
export GeneralCancellationCapPin
  (Choice Applicable selected selected_spec oriented coefficients template valid template_denote delta records)
end DP
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
namespace PC
export PairedPinsControlled (targetTables targetValue)
end PC
set_option backward.isDefEq.respectTransparency false

variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀t,IsAlgebraic ℚ (M t))
local instance originalAlgebra : Algebra ℚ (Original.field M) := (Original.field M).algebra'

abbrev actualM := Original.fieldSignature M

def templates (i : ℕ) : Template where
  boundary := Base.pairArity i
  vertices := if i<1 then (identityTemplate (fun _=>4) i).vertices else (DP.template (actualM M) (DP.selected M)).vertices
  edges := if i<1 then (identityTemplate (fun _=>4) i).edges else (DP.template (actualM M) (DP.selected M)).edges

theorem old_template : templates M 0=identityTemplate (fun _=>4) 0 := rfl
theorem new_template : templates M 1=DP.template (actualM M) (DP.selected M) := rfl
theorem arity_exact : sourceArity (templates M)=Base.pairArity := rfl

theorem valid : ∀i<2,(templates M i).WellFormed 1 1 (fun _=>4) := by
  intro i hi
  interval_cases i
  · exact identityTemplate_wellFormed (fun _=>4) (0 : Fin 1)
  · exact DP.valid (actualM M) (DP.selected M)

def coordinates := (PC.targetTables (s:=1) (a:=fun _=>4) (F M halg) (Base.dictionary M)
  (PairedPinsSemantics.pin false) (PairedPinsSemantics.pin true)
  (fun _ : Fin 1=>Signature.disequality)).vertex

def scale : Original.field M := (DP.oriented (actualM M) (DP.selected M)).1

theorem field_oriented_first (k : DP.Choice) :
    ((DP.oriented (actualM M) k).1 : L)=(DP.oriented M k).1 := by
  rcases k with ⟨c,rev⟩
  fin_cases c <;> cases rev <;> rfl

theorem field_oriented_second (k : DP.Choice) :
    ((DP.oriented (actualM M) k).2 : L)=(DP.oriented M k).2 := by
  rcases k with ⟨c,rev⟩
  fin_cases c <;> cases rev <;> rfl

theorem original_scale : (scale M : L)=(DP.oriented M (DP.selected M)).1 :=
  field_oriented_first M (DP.selected M)

theorem field_even (hM : EvenSupport M) : EvenSupport (actualM M) := by
  intro t ht
  apply Subtype.ext
  exact hM t ht

theorem field_zero (h : DP.Applicable M) : (DP.oriented (actualM M) (DP.selected M)).2=0 := by
  apply Subtype.ext
  rw [field_oriented_second]
  exact (DP.selected_spec M h).2

theorem scale_ne_zero (h : DP.Applicable M) : scale M≠0 := by
  intro hz
  have hc := congrArg (fun z : Original.field M=>(z : L)) hz
  rw [original_scale] at hc
  exact (DP.selected_spec M h).1 hc

theorem decoded_original :
    (fun (i : Fin 1) x=>(F M halg).decode ((Original.tables M halg).vertex i x))=
      fun _ : Fin 1=>actualM M := by
  funext i x
  apply Subtype.ext
  exact familyCoordinates_spec (Original.coefficient M) (Original.coefficient_algebraic M halg) (.inl ⟨i,x⟩)

theorem decoded_edges :
    (fun (i : Fin 1) x y=>(F M halg).decode ((Original.tables M halg).edge i x y))=
      fun _ : Fin 1=>Signature.disequality :=
  kernels_exact M halg

theorem decoded_coordinates (i : Fin 2) :
    (fun x=>(F M halg).decode (coordinates M halg i x))=Base.pairSignatures M i := by
  funext x
  simp only [coordinates,PC.targetTables,LinearEquiv.apply_symm_apply,Base.pairSignatures]

attribute [local irreducible] Template.network Network.denote

/-- Both literal template identities are derived from the original tables;
no local denotation or scalar certificate is a caller parameter. -/
theorem template_denote (hM : EvenSupport M) (h : DP.Applicable M) (i : Fin 2) :
    ((templates M i.val).network (valid M i.val i.isLt)
      (fun j x=>(F M halg).decode ((Original.tables M halg).vertex j x))
      (fun j x y=>(F M halg).decode ((Original.tables M halg).edge j x y))).denote=
      (if i.val=1 then scale M else 1) • (fun x=>(F M halg).decode (coordinates M halg i x)) := by
  rw [decoded_original,decoded_edges,decoded_coordinates]
  fin_cases i
  · change ((identityTemplate (fun _=>4) 0).network (arity:=fun _=>4) _ (fun _ : Fin 1=>actualM M)
        (fun _ : Fin 1=>Signature.disequality)).denote=1 • Base.pairSignatures M 0
    have hold : Base.pairSignatures M (0 : Fin 2)=actualM M := by
      funext x
      rfl
    rw [hold,one_smul]
    exact identityTemplate_denote (fun _=>4) (0 : Fin 1)
      (fun _ : Fin 1=>actualM M) (fun _ : Fin 1=>Signature.disequality)
  · change ((DP.template (actualM M) (DP.selected M)).network (arity:=fun _=>4) _ (fun _ : Fin 1=>actualM M)
        (fun _ : Fin 1=>Signature.disequality)).denote=scale M • Base.pairSignatures M 1
    rw [DP.template_denote (actualM M) (field_even M hM) (DP.selected M) (field_zero M h)]
    congr 1
    funext x
    exact (PairedPinsSemantics.target_pin_signature (s:=1) (a:=fun _=>4) (Base.dictionary M) x).symm

abbrev generatedValue := (sourceTables (templates M) (Original.tables M halg) (coordinates M halg)).evaluate (F M halg)

theorem source_value (r : Base.PairInput) : generatedValue M halg r=Base.pairValue M halg r := by
  change (sourceTables (templates M) (Original.tables M halg) (coordinates M halg)).evaluate (F M halg) r=
    (PC.targetTables (s:=1) (a:=fun _=>4) (F M halg) (Base.dictionary M)
      (PairedPinsSemantics.pin false) (PairedPinsSemantics.pin true)
      (fun _ : Fin 1=>Signature.disequality)).evaluate (F M halg) r
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [sourceTables,coordinates,PC.targetTables,LinearEquiv.apply_symm_apply]
  rw [decoded_edges]
  rfl

def substitution (hM : EvenSupport M) (h : DP.Applicable M) :
    LengthControlledOracleReduction Base.pairEncoding (F M halg).encoding
      Original.targetEncoding (F M halg).encoding (generatedValue M halg) (Original.targetValue M halg) :=
  Cap.controlledSubstitution (F M halg) (templates M) (valid M)
    (Original.tables M halg) (coordinates M halg) 1 (scale M) (scale_ne_zero M h)
    (template_denote M halg hM h)

attribute [local irreducible] substitution

/-- Sole original-palette source. Only output specification is aligned;
all physical programme, clock, query/answer and storage-control data stay put. -/
def source (hM : EvenSupport M) (h : DP.Applicable M) :
    LengthControlledOracleReduction Base.pairEncoding (F M halg).encoding
      Original.targetEncoding (F M halg).encoding (Base.pairValue M halg) (Original.targetValue M halg) where
  reduction := {
    machine := (substitution M halg hM h).reduction.machine
    time := (substitution M halg hM h).reduction.time
    correct oracle ho r := by
      simpa only [source_value] using (substitution M halg hM h).reduction.correct oracle ho r }
  targetOutput := (substitution M halg hM h).targetOutput
  queryBound := (substitution M halg hM h).queryBound
  safeQuery := (substitution M halg hM h).safeQuery


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPairAccess
