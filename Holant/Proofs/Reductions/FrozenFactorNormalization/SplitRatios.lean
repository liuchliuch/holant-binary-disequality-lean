import Holant.Proofs.Reductions.FrozenFactorNormalization.KeyMap
import Holant.Proofs.FiniteGroups.Stabilization.FactorExposure


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L E : Type*} [Field L] [Field E] (φ : L →+* E)
variable {f a b : AnySignature E} (S : ProperSplit f a b) (hf : f.2 ≠ 0)
variable (U : KeyLift φ f)

def joinWord (x : Fin a.1 → Bool) (y : Fin b.1 → Bool) : Fin f.1 → Bool :=
  fun i => Sum.elim x y (S.ports.symm i)

theorem joinWord_left (x : Fin a.1 → Bool) (y : Fin b.1 → Bool) (i : Fin a.1) :
    joinWord S x y (S.ports (.inl i)) = x i := by simp [joinWord]
theorem joinWord_right (x : Fin a.1 → Bool) (y : Fin b.1 → Bool) (i : Fin b.1) :
    joinWord S x y (S.ports (.inr i)) = y i := by simp [joinWord]
theorem joinWord_eta (x : Fin f.1 → Bool) :
    joinWord S (fun i => x (S.ports (.inl i))) (fun i => x (S.ports (.inr i))) = x := by
  funext i
  obtain ⟨j,rfl⟩ := S.ports.surjective i
  cases j <;> simp [joinWord]

def leftWord := firstWord a.2 (S.factors_nonzero hf).1
def rightWord := firstWord b.2 (S.factors_nonzero hf).2
def multiplier : E := (f.2 (firstWord f.2 hf))⁻¹ * (S.scale : E)
theorem multiplier_nonzero : multiplier S hf ≠ 0 :=
  mul_ne_zero (inv_ne_zero (firstWord_nonzero f.2 hf)) S.scale.ne_zero

theorem slice_map (x : Fin a.1 → Bool) (y : Fin b.1 → Bool) :
    φ (U.table (joinWord S x y)) = multiplier S hf * (a.2 x * b.2 y) := by
  have h := congrFun U.equation (joinWord S x y)
  rw [canonicalKey_of_ne_zero f.2 hf] at h
  change φ (U.table (joinWord S x y)) = (f.2 (firstWord f.2 hf))⁻¹ * f.2 (joinWord S x y) at h
  have hs := congrFun S.equation (joinWord S x y)
  have hs' : f.2 (joinWord S x y) = (S.scale : E) * (a.2 x * b.2 y) := by
    simpa [joinWord] using hs
  rw [hs'] at h
  simpa only [multiplier,mul_assoc] using h

def denominator : L := U.table (joinWord S (leftWord S hf) (rightWord S hf))
theorem denominator_nonzero : denominator φ S hf U ≠ 0 := by
  intro hz
  have he := slice_map φ S hf U (leftWord S hf) (rightWord S hf)
  have hn := mul_ne_zero (multiplier_nonzero S hf)
    (mul_ne_zero (firstWord_nonzero a.2 (S.factors_nonzero hf).1)
      (firstWord_nonzero b.2 (S.factors_nonzero hf).2))
  apply hn
  change multiplier S hf * (a.2 (leftWord S hf) * b.2 (rightWord S hf)) = 0
  rw [←he]
  change φ (denominator φ S hf U) = 0
  rw [hz,map_zero]

def leftTable (x : Fin a.1 → Bool) : L :=
  U.table (joinWord S x (rightWord S hf)) / denominator φ S hf U
def rightTable (y : Fin b.1 → Bool) : L :=
  U.table (joinWord S (leftWord S hf) y) / denominator φ S hf U

theorem leftTable_map : RH.mapSignature φ (leftTable φ S hf U) = canonicalKey a.2 := by
  funext x
  change φ (U.table (joinWord S x (rightWord S hf)) / denominator φ S hf U) = _
  rw [map_div₀,slice_map φ S hf U,denominator,slice_map φ S hf U,canonicalKey_of_ne_zero _ (S.factors_nonzero hf).1]
  simp only [Pi.smul_apply,smul_eq_mul,leftWord,rightWord]
  field_simp [multiplier_nonzero S hf,firstWord_nonzero a.2 (S.factors_nonzero hf).1,
    firstWord_nonzero b.2 (S.factors_nonzero hf).2] <;> ring

theorem rightTable_map : RH.mapSignature φ (rightTable φ S hf U) = canonicalKey b.2 := by
  funext y
  change φ (U.table (joinWord S (leftWord S hf) y) / denominator φ S hf U) = _
  rw [map_div₀,slice_map φ S hf U,denominator,slice_map φ S hf U,canonicalKey_of_ne_zero _ (S.factors_nonzero hf).2]
  simp only [Pi.smul_apply,smul_eq_mul,leftWord,rightWord]
  field_simp [multiplier_nonzero S hf,firstWord_nonzero a.2 (S.factors_nonzero hf).1,
    firstWord_nonzero b.2 (S.factors_nonzero hf).2] <;> ring

def leftLift : KeyLift φ a := ⟨leftTable φ S hf U,leftTable_map φ S hf U⟩
def rightLift : KeyLift φ b := ⟨rightTable φ S hf U,rightTable_map φ S hf U⟩

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization
