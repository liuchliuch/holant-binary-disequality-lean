import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalOriginalField
import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalReduction

/-! Literal raw-table identities for the two separately generated original
fields used by tensor-power removal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalOriginalTables
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open UniversalPairReduction.Surgery
namespace F
export GeneralEOTensorPowerRemovalOriginalField
  (family sourceFamily targetFamily sourceField targetField embedding old distinguished target)
end F
namespace R
export GeneralEOTensorPowerRemovalRaw (sourceArity targetArity)
end R
namespace V
export GeneralEOTensorPowerRemovalValue (sourceTable targetTable tensorList)
end V
namespace T
export GeneralEOTensorPowerRemovalTables (signatures listValue tensorList_blockPower)
end T
namespace C
export Holant.LocalDrafts.Hardness.GeneralExtraction.Carrier (blockPower)
end C
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables (castSignature)
end OT
set_option backward.isDefEq.respectTransparency false
variable {s n : ℕ} {a : ℕ → ℕ}

theorem getD_cast {u v : ℕ} (h : u=v) (x : Fin v → Bool) (i : Fin u) :
    (List.ofFn x).getD i.val false=x (Fin.cast h i) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn,←h] using i.isLt)]
  simp only [List.getElem_ofFn]
  rfl

theorem ofFn_cast {u v : ℕ} (h : u=v) (x : Fin v → Bool) :
    List.ofFn (fun i : Fin u => x (Fin.cast h i))=List.ofFn x := by
  subst v
  rfl

variable {K L : Type} [Field K] [Field L]

omit [Field K] in
theorem cast_apply {u v : ℕ} (h : u=v) (f : Signature K u) (x : Fin v → Bool) :
    OT.castSignature h f x=f (fun i => x (Fin.cast h i)) := by
  subst v
  rfl

omit [Field K] in
theorem listValue_ofFn (f : Signature K n) (x : Fin n → Bool) :
    T.listValue f (List.ofFn x)=f x := by
  unfold T.listValue
  congr 1
  funext i
  exact getD_cast rfl x i

theorem family_table (G : (i : Fin s) → Signature K (a i.val)) (f : Signature K n)
    (i : Fin (s+1)) (x : Fin (R.sourceArity s n a i.val) → Bool) :
    F.family G f i x=
      T.signatures (R.sourceArity s n a) (V.sourceTable s (Choice.table G) (T.listValue f)) i x := by
  classical
  unfold F.family T.signatures V.sourceTable
  by_cases h : i.val<s
  · simp only [dite_eq_left h,ite_eq_left h,Choice.table,cast_apply]
    congr 1
    funext j
    exact (getD_cast (by simp [R.sourceArity,h]) x j).symm
  · simp only [dite_eq_right h,ite_eq_right h,cast_apply,T.listValue]
    congr 1
    funext j
    exact (getD_cast (by simp [R.sourceArity,h]) x j).symm

theorem family_map (φ : K →+* L) (G : (i : Fin s) → Signature K (a i.val))
    (f : Signature K n) (i : Fin (s+1)) (x : Fin (R.sourceArity s n a i.val) → Bool) :
    φ (F.family G f i x)=F.family (fun i x => φ (G i x)) (fun x => φ (f x)) i x := by
  classical
  unfold F.family
  split_ifs <;> simp only [cast_apply]

theorem target_table (G : (i : Fin s) → Signature K (a i.val)) (f : Signature K n)
    (k : ℕ) (i : Fin (s+1)) (x : Fin (R.targetArity s n k a i.val) → Bool) :
    T.signatures (R.targetArity s n k a) (V.targetTable s n k (Choice.table G) (T.listValue f)) i x=
      F.family G (C.blockPower f k) i x := by
  classical
  rw [family_table]
  unfold T.signatures V.targetTable V.sourceTable
  by_cases h : i.val<s
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    have hd : k*n=R.targetArity s n k a i.val := by simp [R.targetArity,h]
    rw [←ofFn_cast hd x,T.tensorList_blockPower,listValue_ofFn]

namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalPresentation originalTables originalValue target_exact)
end O
namespace P
export GeneralEOTensorPowerRemovalPadding (Input value)
end P
namespace Q
export GeneralEOTensorPowerRemovalReduction (targetTables)
end Q

variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (f : Signature AlgebraicComplex n) (k : ℕ)
local instance sourceAlgebra : Algebra ℚ (F.sourceField G f) := (F.sourceField G f).algebra'
local instance targetAlgebra : Algebra ℚ (F.targetField G f k) := (F.targetField G f k).algebra'

/-- These are the literal original source coefficients in its generated field. -/
theorem source_coefficient (i : Fin (s+1))
    (x : Fin (R.sourceArity s n a i.val) → Bool) :
    F.family (F.old G f) (F.distinguished G f) i x=
      fieldCoefficient (O.coefficients (F.sourceFamily G f)) ⟨i,x⟩ := by
  apply Subtype.ext
  exact family_map (F.sourceField G f).subtype (F.old G f) (F.distinguished G f) i x

/-- Product coefficients lie in the smaller target field and embed as the
literal list tensor row used by the grouping machine. -/
theorem target_coefficient (i : Fin (s+1))
    (x : Fin (R.targetArity s n k a i.val) → Bool) :
    F.embedding G f k (F.target G f k i x)=
      T.signatures (R.targetArity s n k a)
        (V.targetTable s n k (Choice.table (F.old G f)) (T.listValue (F.distinguished G f))) i x := by
  rw [target_table]
  apply Subtype.ext
  have hm := family_map (F.sourceField G f).subtype (F.old G f)
    (C.blockPower (F.distinguished G f) k) i x
  have hp : (fun y => (F.sourceField G f).subtype
      (C.blockPower (F.distinguished G f) k y))=C.blockPower f k := by
    funext y
    simp only [C.blockPower,map_prod]
    rfl
  have hc := congrArg (fun g : Signature AlgebraicComplex (k*n) => F.family G g i x) hp
  exact (GeneralEOTensorPowerRemovalOriginalField.embedding_coe G f k (F.target G f k i x)).trans
    ((GeneralEOTensorPowerRemovalOriginalField.target_coe G f k i x).trans (hm.trans hc).symm)

/-- The source evaluator is exactly the original-family network value. -/
theorem source_value (r : P.Input s n a) :
    P.value (Choice.table (F.old G f)) (T.listValue (F.distinguished G f)) r=
      O.originalValue (F.sourceFamily G f) r := by
  unfold P.value
  rw [←GeneralEOTensorPowerRemovalTables.denote r.val r.property]
  have hc : T.signatures (R.sourceArity s n a)
      (V.sourceTable s (Choice.table (F.old G f)) (T.listValue (F.distinguished G f)))=
      fun i x => fieldCoefficient (O.coefficients (F.sourceFamily G f)) ⟨i,x⟩ := by
    funext i x
    rw [←family_table]
    exact source_coefficient G f i x
  rw [hc]
  rw [O.originalValue,ExactSignatureTables.evaluate_eq_decoded]
  simp only [O.originalTables,LinearEquiv.apply_symm_apply]

/-- The target uses its own original presentation without a codec-equality
assumption or adjoining the distinguished source coefficients. -/
theorem target_tables :
    Q.targetTables (O.originalPresentation (F.targetFamily G f k)) k (F.target G f k)=
      O.originalTables (F.targetFamily G f k) := rfl

theorem target_value (q : ExactSignatureTables.Input (s+1) 1 (R.targetArity s n k a)) :
    (Q.targetTables (O.originalPresentation (F.targetFamily G f k)) k (F.target G f k)).evaluate
      (O.originalPresentation (F.targetFamily G f k)) q=O.originalValue (F.targetFamily G f k) q := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalOriginalTables
