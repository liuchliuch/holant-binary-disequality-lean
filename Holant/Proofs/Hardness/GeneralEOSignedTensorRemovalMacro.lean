import Holant.Proofs.Hardness.GeneralEOSignedTensorRemovalField
import Holant.Proofs.Hardness.GeneralEOSignedTensorRemovalPalette
import Holant.Proofs.Algorithms.TableFieldTransport

/-! Original-generated augmented-family removal through an actual scalar
macro. The field inclusion has a real rational-coordinate decoder, followed by
the literal scaled-adjoin interpreter. No equality of answer codecs is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalMacro
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
namespace D
export GeneralEOSignedTensorRemovalField (augmented row embedding scalar scalar_nonzero lifted_value)
end D
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue)
end O
namespace A
export GeneralEOTensorPowerRemovalOriginalField (family family_old family_new oldLabel newLabel)
end A
namespace R
export GeneralEOTensorPowerRemovalRaw (sourceArity)
end R
namespace M
export GeneralOddHigherResidueQuaternaryMacro
  (G arity signatures sourceValue old_signature new_signature remove source_value_eq)
end M
namespace P
export GeneralEOSignedTensorRemovalPalette (value revalue retype)
end P
namespace B
export GeneralEONonARSPinningFieldBridge (lift labels native)
end B
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local irreducible] GeneralOddHigherResidueQuaternaryMacro.remove
attribute [local irreducible] GeneralEOSignedTensorRemovalPalette.revalue
attribute [local irreducible] GeneralEOSignedTensorRemovalPalette.retype
private theorem cast_apply {K : Type} {u v : ℕ} (h : u=v) (f : Signature K u)
    (x : Fin v→Bool) : Holant.LocalDrafts.BinaryInterpolation.OriginalTables.castSignature h f x=
      f (fun i => x (Fin.cast h i)) := by
  subst v
  rfl

/-- This small transport fact is proved here to avoid importing the entire
separate tensor-power machine just for a coefficient identity. -/
private theorem family_map {K L : Type} [Field K] [Field L] {s n : ℕ} {a : ℕ→ℕ}
    (φ : K→+*L) (G : (i : Fin s)→Signature K (a i.val)) (f : Signature K n)
    (i : Fin (s+1)) (x : Fin (R.sourceArity s n a i.val)→Bool) :
    φ (A.family G f i x)=A.family (fun j y => φ (G j y)) (fun y => φ (f y)) i x := by
  classical
  unfold GeneralEOTensorPowerRemovalOriginalField.family
  split_ifs <;> simp only [cast_apply]

variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance baseAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (f : Signature AlgebraicComplex n) (hf : ∀x,f x∈O.originalField G)
local instance augmentedAlgebra : Algebra ℚ (O.originalField (D.augmented G f)) :=
  (O.originalField (D.augmented G f)).algebra'

abbrev F := O.originalPresentation G
abbrev T := O.originalTables G
abbrev H := D.augmented G f
abbrev fieldFamily := A.family (M.G (F G) (T G)) (D.row G f hf)

variable (N : Network AlgebraicComplex n) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀e,N.edge e=Signature.disequality)
variable (c : AlgebraicComplex) (hc : c≠0) (hv : N.denote=c • f)
variable (unit : Fin n→Bool) (hu : f unit=1)

abbrev lifted := B.lift G N NL
abbrev labels := B.labels G N NL
abbrev scale := D.scalar G N NL unit

theorem macro_arity : M.arity (lifted G N NL) (labels G N NL)=R.sourceArity s n a := by
  funext i
  by_cases hi : i<s
  · simp [M.arity,sourceArity,Adjoin.templates,R.sourceArity,hi,identityTemplate]
  · simp [M.arity,sourceArity,Adjoin.templates,R.sourceArity,hi]

include hN hn hc hv hu in
theorem macro_rows : ∀i : Fin (s+1),
    (⟨M.arity (lifted G N NL) (labels G N NL) i.val,
      M.signatures (F G) (T G) (lifted G N NL) (labels G N NL) (scale G N NL unit) i⟩ :
      AnySignature (O.originalField G))=
    ⟨R.sourceArity s n a i.val,fieldFamily G f hf i⟩ := by
  intro i
  by_cases hi : i.val<s
  · let j : Fin s := ⟨i.val,hi⟩
    have he : i=j.castSucc := Fin.ext rfl
    rw [he]
    exact (M.old_signature (F G) (T G) (lifted G N NL) (labels G N NL)
      (scale G N NL unit) j).trans
      (A.family_old (M.G (F G) (T G)) (D.row G f hf) j).symm
  · have he : i=⟨s,Nat.lt_succ_self s⟩ := by apply Fin.ext; change i.val=s; omega
    rw [he]
    exact (M.new_signature (F G) (T G) (lifted G N NL) (labels G N NL)
      (scale G N NL unit) (GeneralEOSinglePinSource.native_tables G)
      (GeneralOddHigherResidueQuaternaryPinning.lifted_labels G N NL)
      (B.native G N NL)
      (D.scalar_nonzero G f N NL hN hn c hc hv unit hu) (D.row G f hf)
      (D.lifted_value G f hf N NL hN hn c hv unit hu)).trans
      (A.family_new (M.G (F G) (T G)) (D.row G f hf)).symm

include hN hn hc hv hu in
def sameField : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1 (R.sourceArity s n a)) (F G).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding
    (P.value (fieldFamily G f hf)) (O.originalValue G) := by
  let r : LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) 1 (M.arity (lifted G N NL) (labels G N NL)))
      (F G).encoding (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding
      (M.sourceValue (F G) (T G) (lifted G N NL) (labels G N NL) (scale G N NL unit))
      (O.originalValue G) := M.remove (F G) (T G) (lifted G N NL) (labels G N NL) (scale G N NL unit)
    (D.scalar_nonzero G f N NL hN hn c hc hv unit hu)
  have r' : LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) 1 (M.arity (lifted G N NL) (labels G N NL)))
      (F G).encoding (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding
      (P.value (M.signatures (F G) (T G) (lifted G N NL) (labels G N NL) (scale G N NL unit)))
      (O.originalValue G) := P.revalue r (fun q => congrFun
    (M.source_value_eq (F G) (T G) (lifted G N NL) (labels G N NL)
      (scale G N NL unit) (GeneralEOSinglePinSource.native_tables G)) q)
  exact P.retype (F G) (macro_arity G N NL) _ (fieldFamily G f hf)
    (macro_rows G f hf N NL hN hn c hc hv unit hu) r'

attribute [local irreducible] sameField

abbrev mappedTables := TableFieldTransport.mapTables (O.originalPresentation (H G f))
  (F G) (D.embedding G f hf) (O.originalTables (H G f))

theorem mapped_vertex (i : Fin (s+1)) (x : Fin (R.sourceArity s n a i.val)→Bool) :
    (F G).decode ((mappedTables G f hf).vertex i x)=fieldFamily G f hf i x := by
  apply Subtype.ext
  simp only [mappedTables,TableFieldTransport.mapTables,O.originalTables,LinearEquiv.apply_symm_apply]
  change H G f i x=(fieldFamily G f hf i x : AlgebraicComplex)
  have hold : (fun j y => (M.G (F G) (T G) j y : AlgebraicComplex))=G := by
    funext j y
    change ((F G).decode ((T G).vertex j y) : AlgebraicComplex)=G j y
    simp only [T,O.originalTables,LinearEquiv.apply_symm_apply]
    rfl
  have hnew : (fun y => (D.row G f hf y : AlgebraicComplex))=f := rfl
  have hm := family_map (O.originalField G).subtype
    (M.G (F G) (T G)) (D.row G f hf) i x
  change (A.family (M.G (F G) (T G)) (D.row G f hf) i x : AlgebraicComplex)=
    A.family (fun j y => (M.G (F G) (T G) j y : AlgebraicComplex))
      (fun y => (D.row G f hf y : AlgebraicComplex)) i x at hm
  rw [hold,hnew] at hm
  exact hm.symm

theorem mapped_value (q : ExactSignatureTables.Input (s+1) 1 (R.sourceArity s n a)) :
    (mappedTables G f hf).evaluate (F G) q=P.value (fieldFamily G f hf) q := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  have hv : (fun i x => (F G).decode ((mappedTables G f hf).vertex i x))=fieldFamily G f hf :=
    funext fun i => funext fun x => mapped_vertex G f hf i x
  rw [hv]
  have he : (fun i x y => (F G).decode ((mappedTables G f hf).edge i x y))=
      (fun _ : Fin 1 => Signature.disequality) := by
    funext i x y
    simp only [mappedTables,TableFieldTransport.mapTables,O.originalTables,
      LinearEquiv.apply_symm_apply]
    cases x <;> cases y <;> simp [Signature.disequality]
  rw [he]

include hN hn hc hv hu in
/-- The source and target are both literal original-family presentations.
The target oracle contains only the old G labels, and every macro occurrence
is charged and corrected by the actual nonzero original-field scale. -/
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1 (R.sourceArity s n a))
    (O.originalPresentation (H G f)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (F G).encoding
    (O.originalValue (H G f)) (O.originalValue G) :=
  C.composeControlled
    (TableFieldTransport.fromOriginal (O.originalPresentation (H G f))
      (F G) (D.embedding G f hf) (O.originalTables (H G f)))
    (P.revalue (sameField G f hf N NL hN hn c hc hv unit hu)
      (fun q => (mapped_value G f hf q).symm))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalMacro
