import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalTables
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget
import Holant.Proofs.BinaryInterpolation.OriginalTables

/-! The literal source and tensor-power dictionaries have their own generated
fields. Products of source coefficients prove target-field inclusion; the
distinguished source row is not assumed to belong to the target field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalOriginalField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open scoped BigOperators
namespace R
export GeneralEOTensorPowerRemovalRaw (sourceArity targetArity)
end R
namespace C
export Holant.LocalDrafts.Hardness.GeneralExtraction.Carrier (blockPower)
end C
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue target_exact)
end O
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables (castSignature castSignature_any)
end OT
set_option backward.isDefEq.respectTransparency false
variable {s n : ℕ} {a : ℕ → ℕ}

section Generic
variable {K : Type} [Field K]
variable (G : (i : Fin s) → Signature K (a i.val)) (f : Signature K n)

def family (i : Fin (s+1)) : Signature K (R.sourceArity s n a i.val) :=
  if h : i.val<s then OT.castSignature (by simp [R.sourceArity,h]) (G ⟨i.val,h⟩)
  else OT.castSignature (by simp [R.sourceArity,h]) f

def oldLabel (i : Fin s) : Fin (s+1) := ⟨i.val,Nat.lt_succ_of_lt i.isLt⟩
def newLabel : Fin (s+1) := ⟨s,Nat.lt_succ_self s⟩

theorem family_old (i : Fin s) :
    (⟨R.sourceArity s n a i.val,family G f (oldLabel i)⟩ : AnySignature K)=⟨a i.val,G i⟩ := by
  simp only [family,oldLabel,dite_eq_left i.isLt]
  exact OT.castSignature_any _ _

theorem family_new :
    (⟨R.sourceArity s n a s,family G f (newLabel (s:=s))⟩ : AnySignature K)=⟨n,f⟩ := by
  simp only [family,newLabel,Nat.lt_irrefl,dite_eq_right not_false]
  exact OT.castSignature_any _ _

omit [Field K] in
theorem cast_mem (A : Set K) {u v : ℕ} (h : u=v) (q : Signature K u)
    (hq : ∀x,q x∈A) : ∀x,OT.castSignature h q x∈A := by
  subst v
  exact hq

omit [Field K] in
theorem family_mem (A : Set K) (hG : ∀i x,G i x∈A) (hf : ∀x,f x∈A) :
    ∀i x,family G f i x∈A := by
  intro i
  unfold family
  split_ifs with h
  · exact cast_mem A _ _ (hG ⟨i.val,h⟩)
  · exact cast_mem A _ _ hf
end Generic

variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (f : Signature AlgebraicComplex n) (k : ℕ)

abbrev sourceFamily := family G f
abbrev targetFamily : (i : Fin (s+1)) → Signature AlgebraicComplex (R.targetArity s n k a i.val) :=
  family G (C.blockPower f k)
abbrev sourceField := O.originalField (sourceFamily G f)
abbrev targetField := O.originalField (targetFamily G f k)
local instance sourceAlgebra : Algebra ℚ (sourceField G f) := (sourceField G f).algebra'
local instance targetAlgebra : Algebra ℚ (targetField G f k) := (targetField G f k).algebra'

theorem row_mem (i : Fin (s+1)) (x : Fin (R.sourceArity s n a i.val) → Bool) :
    sourceFamily G f i x∈sourceField G f :=
  coefficient_mem_familyField (O.coefficients (sourceFamily G f)) ⟨i,x⟩

theorem any_mem (q : AnySignature AlgebraicComplex) (i : Fin (s+1))
    (h : (⟨R.sourceArity s n a i.val,sourceFamily G f i⟩ : AnySignature AlgebraicComplex)=q) :
    ∀x,q.2 x∈sourceField G f := by
  subst q
  exact row_mem G f i

theorem old_mem (i : Fin s) (x : Fin (a i.val) → Bool) : G i x∈sourceField G f :=
  any_mem G f ⟨a i.val,G i⟩ (oldLabel i) (family_old G f i) x

theorem distinguished_mem (x : Fin n → Bool) : f x∈sourceField G f :=
  any_mem G f ⟨n,f⟩ newLabel (family_new G f) x

theorem power_mem (x : Fin (k*n) → Bool) : C.blockPower f k x∈sourceField G f := by
  unfold C.blockPower
  exact (sourceField G f).prod_mem (fun _ _ => distinguished_mem G f _)

theorem field_le : targetField G f k≤sourceField G f := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  exact family_mem G (C.blockPower f k) (sourceField G f) (old_mem G f) (power_mem G f k) i x

def embedding : targetField G f k→ₐ[ℚ]sourceField G f :=
  IntermediateField.inclusion (field_le G f k)

@[simp] theorem embedding_coe (x : targetField G f k) :
    (embedding G f k x).val=x.val :=
  IntermediateField.coe_inclusion (field_le G f k) x

def old (i : Fin s) (x : Fin (a i.val) → Bool) : sourceField G f := ⟨G i x,old_mem G f i x⟩
def distinguished (x : Fin n → Bool) : sourceField G f := ⟨f x,distinguished_mem G f x⟩

def target (i : Fin (s+1)) (x : Fin (R.targetArity s n k a i.val) → Bool) : targetField G f k :=
  fieldCoefficient (O.coefficients (targetFamily G f k)) ⟨i,x⟩

@[simp] theorem old_coe (i : Fin s) (x : Fin (a i.val) → Bool) :
    (old G f i x).val=G i x := rfl
@[simp] theorem distinguished_coe (x : Fin n → Bool) :
    (distinguished G f x).val=f x := rfl
@[simp] theorem target_coe (i : Fin (s+1)) (x : Fin (R.targetArity s n k a i.val) → Bool) :
    (target G f k i x).val=targetFamily G f k i x := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalOriginalField
