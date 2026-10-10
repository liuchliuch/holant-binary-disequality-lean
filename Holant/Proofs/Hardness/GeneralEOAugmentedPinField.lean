import Holant.Proofs.Hardness.GeneralEOSignedTensorRemovalField
import Holant.Proofs.Hardness.GeneralEOSinglePinDEQInclusion
import Holant.Proofs.Algorithms.TableFieldTransport

/-! Exact codec transport of literal pin problems into an augmented dictionary.
The old field embeds in the new generated field; their presentations are never
identified. The old and new answer words are converted by the field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAugmentedPinField
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open UniversalPairReduction
open Holant.LocalDrafts.MainChain
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue)
end O
namespace A
export GeneralEOTensorPowerRemovalOriginalField (family family_old family_new oldLabel newLabel old_mem)
end A
namespace P
export GeneralEOSinglePinAmplificationProgramme (sourceValue inputEncoding)
end P
namespace S
export GeneralEOSinglePinAmplificationSemantics (value)
end S
namespace T
export GeneralEOSinglePinAmplificationAccess (tables tables_value)
end T
namespace I
export GeneralEOSinglePinDEQInclusion (source old)
end I
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section Generic
variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
variable {d e s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (J : FixedField L e) (φ : K→ₐ[ℚ]L)
variable (B : ExactSignatureTables d s 1 a)

abbrev mapped := TableFieldTransport.mapTables F J φ B
abbrev pinTables := T.tables F (ValueJoins.signatures F B)

theorem binary_map (G : (i : Fin s)→Signature K (a i.val))
    (i : Fin (s+1)) (x : Fin (extendedArity s a i.val)→Bool) :
    φ (BinaryFamily.signatures G BinaryTable.delta i x)=
      BinaryFamily.signatures (fun j y => φ (G j y)) BinaryTable.delta i x := by
  unfold BinaryFamily.signatures
  split_ifs
  · rfl
  · simp only [BinaryTable.delta]
    split_ifs <;> simp

theorem mapped_pin_value (q : ExactSignatureTables.Input (s+1) 1 (extendedArity s a)) :
    (TableFieldTransport.mapTables F J φ (pinTables F B)).evaluate J q=
      P.sourceValue J (mapped F J φ B) q := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  have hv : (fun i x => J.decode
      ((TableFieldTransport.mapTables F J φ (pinTables F B)).vertex i x))=
      BinaryFamily.signatures (ValueJoins.signatures J (mapped F J φ B)) BinaryTable.delta := by
    funext i x
    simp only [TableFieldTransport.mapTables,pinTables,T.tables,LinearEquiv.apply_symm_apply]
    rw [binary_map φ]
    apply congrArg (fun U : (j : Fin s)→Signature L (a j.val) =>
      BinaryFamily.signatures U BinaryTable.delta i x)
    funext j y
    exact (LinearEquiv.apply_symm_apply J.decode _).symm
  have he : (fun i x y => J.decode
      ((TableFieldTransport.mapTables F J φ (pinTables F B)).edge i x y))=
      (fun _ : Fin 1 => Signature.disequality) := by
    funext i x y
    simp only [TableFieldTransport.mapTables,pinTables,T.tables,LinearEquiv.apply_symm_apply]
    cases x <;> cases y <;> simp [Signature.disequality]
  rw [hv,he]
  rfl

/-- A total rational-coordinate decoder supplies the changed answer codec. -/
def intoField : LengthControlledOracleReduction
    (P.inputEncoding (s:=s) (a:=a)) F.encoding
    (P.inputEncoding (s:=s) (a:=a)) J.encoding
    (P.sourceValue F B) (P.sourceValue J (mapped F J φ B)) := by
  have r := TableFieldTransport.fromOriginal F J φ (pinTables F B)
  have hs : (pinTables F B).evaluate F=P.sourceValue F B :=
    funext fun q => T.tables_value F (ValueJoins.signatures F B) q
  have ht : (TableFieldTransport.mapTables F J φ (pinTables F B)).evaluate J=
      P.sourceValue J (mapped F J φ B) := funext (mapped_pin_value F J φ B)
  rw [hs,ht] at r
  exact r
end Generic

variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (f : Signature AlgebraicComplex n)
abbrev augmented := A.family G f
local instance oldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
local instance augmentedAlgebra : Algebra ℚ (O.originalField (augmented G f)) :=
  (O.originalField (augmented G f)).algebra'

theorem old_le : O.originalField G≤O.originalField (augmented G f) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  exact A.old_mem G f i x

def embedding : O.originalField G→ₐ[ℚ]O.originalField (augmented G f) :=
  IntermediateField.inclusion (old_le G f)

abbrev originalF := O.originalPresentation G
abbrev augmentedF := O.originalPresentation (augmented G f)
abbrev liftedTables := mapped (originalF G) (augmentedF G f) (embedding G f) (O.originalTables G)
abbrev rows := ValueJoins.signatures (augmentedF G f) (O.originalTables (augmented G f))

def ambientAny (z : AnySignature (O.originalField (augmented G f))) :
    AnySignature AlgebraicComplex := ⟨z.1,fun x => (z.2 x).val⟩

theorem ambientAny_injective : Function.Injective (ambientAny G f) := by
  rintro ⟨m,p⟩ ⟨k,q⟩ h
  have hk : m=k := congrArg Sigma.fst h
  subst k
  congr 1
  funext x
  apply Subtype.ext
  exact congrFun (eq_of_heq (Sigma.mk.inj_iff.mp h).2) x

/-- Old ordered rows survive the generated-field embedding literally. -/
theorem old_rows (i : Fin s) :
    (⟨GeneralEOTensorPowerRemovalRaw.sourceArity s n a i.val,rows G f (I.old i)⟩ :
      AnySignature (O.originalField (augmented G f)))=
      ⟨a i.val,ValueJoins.signatures (augmentedF G f) (liftedTables G f) i⟩ := by
  apply ambientAny_injective G f
  simp only [ambientAny,rows,ValueJoins.signatures,liftedTables,mapped,
    TableFieldTransport.mapTables,O.originalTables,LinearEquiv.apply_symm_apply]
  exact A.family_old G f i

/-- Literal G+01 queries embed into [G,f]+01, retaining both faithful codecs. -/
def source : LengthControlledOracleReduction
    (P.inputEncoding (s:=s) (a:=a)) (originalF G).encoding
    (P.inputEncoding (s:=s+1) (a:=GeneralEOTensorPowerRemovalRaw.sourceArity s n a))
      (augmentedF G f).encoding
    (P.sourceValue (originalF G) (O.originalTables G))
    (P.sourceValue (augmentedF G f) (O.originalTables (augmented G f))) :=
  C.composeControlled
    (intoField (originalF G) (augmentedF G f) (embedding G f) (O.originalTables G))
    (I.source (augmentedF G f) (liftedTables G f) (rows G f) (old_rows G f))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAugmentedPinField
