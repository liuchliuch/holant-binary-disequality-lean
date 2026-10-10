import Holant.Certificates.PlatonicAtlas.Orbits
import Holant.Certificates.TetrahedralBridge.Normalization
import Holant.Certificates.RainbowOrbit.GroupActions
import Holant.Certificates.PlatonicIncidence.DomainGraph

/-! Actual two-port domain operations.  The transpose flag is a literal swap
of the two contracted ports; the other factors are current group directions. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure DomainAction (g : PlatonicModel) where
  left : Mat
  right : Mat
  swap : Bool
  left_mem : groupDirection g left
  right_mem : groupDirection g right

def DomainAction.apply {g : PlatonicModel} (D : DomainAction g) (K : Mat) : Mat :=
  D.left * (if D.swap then K.transpose else K) * D.right

def DomainAction.linear {g : PlatonicModel} (D : DomainAction g) : Mat →ₗ[ℂ] Mat where
  toFun := D.apply
  map_add' K H := by cases hs : D.swap <;> simp [DomainAction.apply,hs,mul_add,add_mul]
  map_smul' c K := by cases hs : D.swap <;> simp [DomainAction.apply,hs]

@[simp] theorem DomainAction.linear_apply {g : PlatonicModel} (D : DomainAction g) (K : Mat) :
    D.linear K=D.apply K := rfl

theorem DomainAction.mem {g : PlatonicModel} (D : DomainAction g) {K : Mat}
    (hK : groupDirection g K) : groupDirection g (D.apply K) := by
  apply groupDirection_mul g _ D.right_mem
  apply groupDirection_mul g D.left_mem
  cases hs : D.swap <;> simp only [hs,Bool.false_eq_true,if_false,if_true]
  · exact hK
  · exact direction_transpose g hK

theorem DomainAction.injective {g : PlatonicModel} (D : DomainAction g) :
    Function.Injective D.linear := by
  intro K H he
  have hl := Matrix.nonsing_inv_mul D.left
    (isUnit_iff_ne_zero.mpr (groupDirection_det_ne_zero g D.left_mem))
  have hr := Matrix.mul_nonsing_inv D.right
    (isUnit_iff_ne_zero.mpr (groupDirection_det_ne_zero g D.right_mem))
  have hh := congrArg (fun T : Mat => D.left⁻¹*T*D.right⁻¹) he
  change D.left⁻¹*(D.left*(if D.swap then K.transpose else K)*D.right)*D.right⁻¹ =
    D.left⁻¹*(D.left*(if D.swap then H.transpose else H)*D.right)*D.right⁻¹ at hh
  have hc (T : Mat) : D.left⁻¹*(D.left*T*D.right)*D.right⁻¹=T := by
    calc D.left⁻¹*(D.left*T*D.right)*D.right⁻¹ =
        (D.left⁻¹*D.left)*T*(D.right*D.right⁻¹) := by simp only [mul_assoc]
      _ = T := by rw [hl,hr,one_mul,mul_one]
  rw [hc,hc] at hh
  cases hs : D.swap <;> simp only [hs,Bool.false_eq_true,if_false,if_true] at hh
  · exact hh
  · exact Matrix.transpose_injective hh

def DomainAction.equiv {g : PlatonicModel} (D : DomainAction g) : Mat ≃ₗ[ℂ] Mat :=
  LinearEquiv.ofBijective D.linear ⟨D.injective,
    (LinearMap.injective_iff_surjective).mp D.injective⟩

@[simp] theorem DomainAction.equiv_apply {g : PlatonicModel} (D : DomainAction g) (K : Mat) :
    D.equiv K=D.apply K := rfl

/-- Composition keeps the exact two local matrices and whether the original
contracted pair is reversed. -/
def DomainAction.comp {g : PlatonicModel} (D E : DomainAction g) : DomainAction g where
  left := D.left * (if D.swap then E.right.transpose else E.left)
  right := (if D.swap then E.left.transpose else E.right) * D.right
  swap := xor D.swap E.swap
  left_mem := groupDirection_mul g D.left_mem (by
    cases hs : D.swap <;> simp only [hs,Bool.false_eq_true,if_false,if_true]
    · exact E.left_mem
    · exact direction_transpose g E.right_mem)
  right_mem := groupDirection_mul g (by
    cases hs : D.swap <;> simp only [hs,Bool.false_eq_true,if_false,if_true]
    · exact E.right_mem
    · exact direction_transpose g E.left_mem) D.right_mem

theorem DomainAction.comp_apply {g : PlatonicModel} (D E : DomainAction g) (K : Mat) :
    (D.comp E).apply K=D.apply (E.apply K) := by
  cases hd : D.swap <;> cases he : E.swap <;>
    simp [DomainAction.comp,DomainAction.apply,hd,he,Matrix.transpose_mul,mul_assoc]

def normalTriangle : Fin 3 → Mat :=
  ![TetrahedralBridge.normalPlus,TetrahedralBridge.normalMinus,Matrix.of Q0]

def normalIndex : (g : PlatonicModel) → Fin 3 → Fin (size g)
  | .tetrahedral => (![4,11,0] : Fin 3 → Fin 12)
  | .octahedral => (![4,11,0] : Fin 3 → Fin 24)
  | .icosahedral => (![4,11,0] : Fin 3 → Fin 60)

theorem normalIndex_injective (g : PlatonicModel) : Function.Injective (normalIndex g) := by
  cases g <;> decide

theorem normal_representative (g : PlatonicModel) (r : Fin 3) :
    representative g (normalIndex g r)=normalTriangle r := by
  cases g <;> fin_cases r <;> ext a b <;> cases a <;> cases b <;>
    simp [normalIndex,normalTriangle,TetrahedralBridge.normalPlus,TetrahedralBridge.normalMinus,
      representative,raw,tetrahedralRaw,octahedralRaw,icosahedralRaw,goldenMatrix,GoldenInt.eval,
      quaternion,Q0,Q1,Q2,Q3,Signature.equality,sub_eq_add_neg]

theorem normalTriangle_mem (g : PlatonicModel) (r : Fin 3) : groupDirection g (normalTriangle r) := by
  rw [←normal_representative g r]
  exact representative_mem g _

theorem normalTriangle_nonzero (r : Fin 3) : normalTriangle r≠0 := by
  rw [←normal_representative .tetrahedral r]
  exact representative_ne_zero .tetrahedral _

theorem normalTriangle_faithful (r s : Fin 3) {c : ℂ}
    (he : normalTriangle r=c • normalTriangle s) : r=s := by
  rw [←normal_representative .tetrahedral r,←normal_representative .tetrahedral s] at he
  exact normalIndex_injective .tetrahedral (projectively_injective .tetrahedral _ _ c he)

theorem normal_seed (g : PlatonicModel) :
    Holant.Certificates.PlatonicIncidence.baseLine g (Holant.Certificates.PlatonicAtlas.seed g 3)=
      Finset.univ.image (normalIndex g) := by
  cases g <;> decide

theorem normalTriangle_relation : normalTriangle 0+normalTriangle 1=(2 : ℂ) • normalTriangle 2 := by
  ext a b
  simp only [normalTriangle,TetrahedralBridge.normalPlus,TetrahedralBridge.normalMinus,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.cons_val_fin_one,
    Matrix.add_apply,Matrix.sub_apply,Matrix.of_apply,Matrix.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  ring

end
end Holant.Platonic.RankDeficientLocalization.Normalization
