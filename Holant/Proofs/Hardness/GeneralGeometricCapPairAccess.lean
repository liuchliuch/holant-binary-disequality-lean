import Holant.Proofs.Hardness.GeneralGeometricCapInterpolation
import Holant.Proofs.Hardness.GeneralCancellationCapPairAccess
import Holant.Proofs.BinaryInterpolation.FieldSource
import Holant.Proofs.Hardness.ValidatedInputTransport

/-! Literal unequal-norm original coefficients choose an oriented cap internally.
The original generated field and its encoding are retained throughout. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapPairAccess
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
namespace Local
export GeneralGeometricCapLocal (Applicable infinite_of_unequal_norms)
end Local
namespace Cap
export GeneralCancellationCapPin (Choice oriented)
end Cap
namespace Base
export SparseOriginalPairAccess (PairInput pairEncoding pairValue pairSignatures)
end Base
namespace Old
export GeneralCancellationCapPairAccess (actualM field_even field_oriented_first field_oriented_second decoded_original decoded_edges)
end Old
namespace I
export GeneralGeometricCapInterpolation (source sourceValue sourceSignatures targetTables target_value)
end I
variable {L : Type} [NormedField L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀t,IsAlgebraic ℚ (M t))
local instance originalAlgebra : Algebra ℚ (Original.field M) := (Original.field M).algebra'

def selected : Cap.Choice := by
  classical
  exact if h : Local.Applicable M then Classical.choose h else (0,false)

theorem selected_spec (h : Local.Applicable M) :
    (Cap.oriented M (selected M)).1≠0 ∧ (Cap.oriented M (selected M)).2≠0 ∧
    ‖(Cap.oriented M (selected M)).1‖≠‖(Cap.oriented M (selected M)).2‖ := by
  classical
  simpa only [selected,dite_eq_left h] using Classical.choose_spec h

theorem first_nonzero (h : Local.Applicable M) :
    (Cap.oriented (Old.actualM M) (selected M)).1≠0 := by
  intro hz
  have he := congrArg (fun z : Original.field M=>(z : L)) hz
  rw [Old.field_oriented_first] at he
  exact (selected_spec M h).1 he

theorem second_nonzero (h : Local.Applicable M) :
    (Cap.oriented (Old.actualM M) (selected M)).2≠0 := by
  intro hz
  have he := congrArg (fun z : Original.field M=>(z : L)) hz
  rw [Old.field_oriented_second] at he
  exact (selected_spec M h).2.1 he

theorem ratio_infinite (h : Local.Applicable M) (n : ℕ) (hn : 0<n) :
    ((Cap.oriented (Old.actualM M) (selected M)).1/
      (Cap.oriented (Old.actualM M) (selected M)).2)^n≠1 := by
  intro he
  have hc := congrArg (fun z : Original.field M=>(z : L)) he
  change (((Cap.oriented (Old.actualM M) (selected M)).1 : L)/
    ((Cap.oriented (Old.actualM M) (selected M)).2 : L))^n=1 at hc
  rw [Old.field_oriented_first,Old.field_oriented_second] at hc
  exact Local.infinite_of_unequal_norms _ _ (selected_spec M h).2.1 (selected_spec M h).2.2 n hn hc

abbrev arity := Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=1) (fun _=>4)
  (GeneralGeometricCapInterpolation.g (Old.actualM M) (selected M))

theorem arity_eq : arity M=SparseOriginalPairAccess.pairArity := by
  funext i
  by_cases hi : i<1
  · simp [arity,Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A,
      BinaryInterpolation.Chains.Compiler.OriginalFamily.macroArity,sourceArity,
      Adjoin.templates,identityTemplate,SparseOriginalPairAccess.pairArity,
      PairedPinsRaw.targetArity,hi]
  · simp [arity,Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A,
      BinaryInterpolation.Chains.Compiler.OriginalFamily.macroArity,sourceArity,
      Adjoin.templates,SparseOriginalPairAccess.pairArity,PairedPinsRaw.targetArity,hi]

def asInput (r : Base.PairInput) : GeneralGeometricCapInterpolation.Input
    (Old.actualM M) (selected M) (F M halg) :=
  ⟨r.val,by change r.val.WellFormed 2 1 (arity M); rw [arity_eq]; exact r.property⟩

theorem input_bytes (r : Base.PairInput) :
    (GeneralGeometricCapInterpolation.inputEncoding (Old.actualM M) (selected M) (F M halg)).encode
      (asInput M halg r)=Base.pairEncoding.encode r := rfl

/-- Arity transports do not introduce a changed signature palette. -/
theorem signatures_eq (i : Fin 2) :
    (⟨arity M i.val,I.sourceSignatures (Old.actualM M) (selected M) i⟩ : AnySignature (Original.field M))=
      ⟨SparseOriginalPairAccess.pairArity i.val,Base.pairSignatures M i⟩ := by
  fin_cases i
  · exact Holant.LocalDrafts.BinaryInterpolation.OriginalTables.binarySlot_old
        (GeneralGeometricCapInterpolation.g (Old.actualM M) (selected M))
        (GeneralGeometricCapInterpolation.hg (Old.actualM M) (selected M))
        (GeneralGeometricCapInterpolation.original (Old.actualM M))
        (GeneralGeometricCapInterpolation.kernels (K:=Original.field M)) rfl
        (GeneralGeometricCapLocal.anti 1 0) (0 : Fin 1)
  · have he := Holant.LocalDrafts.BinaryInterpolation.OriginalTables.binarySlot_new
        (GeneralGeometricCapInterpolation.g (Old.actualM M) (selected M))
        (GeneralGeometricCapInterpolation.hg (Old.actualM M) (selected M))
        (GeneralGeometricCapInterpolation.original (Old.actualM M))
        (GeneralGeometricCapInterpolation.kernels (K:=Original.field M)) rfl
        (GeneralGeometricCapLocal.anti 1 0)
    apply he.trans
    apply congrArg (fun f : Signature (Original.field M) 2=>(⟨2,f⟩ : AnySignature (Original.field M)))
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [GeneralGeometricCapLocal.anti,BinaryInterpolation.Chains.binarySignature,
        Base.pairSignatures,PairedPinsSemantics.targetSignatures,PairedPinsSemantics.pin,h0,h1]

theorem source_value (r : Base.PairInput) :
    I.sourceValue (Old.actualM M) (selected M) (F M halg) (asInput M halg r)=Base.pairValue M halg r := by
  have he := Holant.LocalDrafts.BinaryInterpolation.FieldSource.raw_value_transport (arity_eq M)
    (I.sourceSignatures (Old.actualM M) (selected M)) (Base.pairSignatures M)
    (signatures_eq M) (fun _ : Fin 1=>Signature.disequality) r.val (asInput M halg r).property r.property
  have hv : Base.pairValue M halg r=
      (r.val.realize r.property (Base.pairSignatures M)
        (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
    simp only [Base.pairValue,PairedPinsControlled.targetValue,
      ExactSignatureTables.evaluate_eq_decoded,PairedPinsControlled.targetTables,
      LinearEquiv.apply_symm_apply]
  rw [hv]
  exact he

theorem target_value (r : Original.TargetInput) :
    (I.targetTables (Old.actualM M) (F M halg)).evaluate (F M halg) r=Original.targetValue M halg r := by
  rw [I.target_value]
  change _=(Original.tables M halg).evaluate (F M halg) r
  rw [ExactSignatureTables.evaluate_eq_decoded,Old.decoded_original,Old.decoded_edges]
  rfl

attribute [local irreducible] GeneralGeometricCapInterpolation.source

def interpolation (hM : EvenSupport M) (h : Local.Applicable M) :
    LengthControlledOracleReduction
      (GeneralGeometricCapInterpolation.inputEncoding (Old.actualM M) (selected M) (F M halg))
      (F M halg).encoding Original.targetEncoding (F M halg).encoding
      (I.sourceValue (Old.actualM M) (selected M) (F M halg)) (Original.targetValue M halg) := by
  have src := I.source (Old.actualM M) (Old.field_even M hM) (selected M) (F M halg)
    (first_nonzero M h) (second_nonzero M h) (ratio_infinite M h)
  have ht : (I.targetTables (Old.actualM M) (F M halg)).evaluate (F M halg)=Original.targetValue M halg := funext (target_value M halg)
  rw [ht] at src
  exact src

attribute [local irreducible] interpolation

def source (hM : EvenSupport M) (h : Local.Applicable M) :
    LengthControlledOracleReduction Base.pairEncoding (F M halg).encoding
      Original.targetEncoding (F M halg).encoding (Base.pairValue M halg) (Original.targetValue M halg) :=
  ValidatedInputTransport.source (interpolation M halg hM h) (asInput M halg)
    (input_bytes M halg) (source_value M halg)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapPairAccess
