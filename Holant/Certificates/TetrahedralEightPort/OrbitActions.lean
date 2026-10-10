import Holant.Certificates.TetrahedralEightPort.OrbitCertificate
import Holant.Certificates.TetrahedralEightPort.OrbitGenerators
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.GroupTheory.Perm.Sign

/-! Actual six-port local matrix actions and port permutations on complex
projective tensors. These are the semantic operations checked by the finite
orbit witnesses, rather than actions on certificate indices. -/
namespace Holant.Certificates.TetrahedralEightPort.OrbitActions
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev SixTensor := Signature ℂ 6
abbrev Point := Projectivization ℂ SixTensor
abbrev Matrix2 := Matrix Bool Bool ℂ

def localLinear (p : Fin 6) (M : Matrix2) : SixTensor →ₗ[ℂ] SixTensor where
  toFun f := fun x => ∑ b : Bool, M (x p) b * f (Function.update x p b)
  map_add' f g := by funext x; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c f := by funext x; simp [mul_left_comm,mul_add]

theorem local_one (p : Fin 6) (f : SixTensor) : localLinear p 1 f = f := by
  funext x
  simp [localLinear,Matrix.one_apply]

theorem local_mul (p : Fin 6) (M N : Matrix2) (f : SixTensor) :
    localLinear p M (localLinear p N f) = localLinear p (M*N) f := by
  funext x
  simp only [localLinear,LinearMap.coe_mk,AddHom.coe_mk,Matrix.mul_apply,
    Fintype.sum_bool,Function.update_self,Function.update_idem]
  ring

theorem local_scale_matrix (p : Fin 6) (c : ℂ) (M : Matrix2) (f : SixTensor) :
    localLinear p (c • M) f = c • localLinear p M f := by
  funext x
  simp [localLinear,mul_assoc,mul_add]

theorem local_injective (p : Fin 6) (M : Matrix2) (hM : M.det ≠ 0) :
    Function.Injective (localLinear p M) := by
  intro f g h
  have he := congrArg (localLinear p M⁻¹) h
  simpa only [local_mul,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),local_one] using he

def localPoint (p : Fin 6) (M : Matrix2) (hM : M.det ≠ 0) : Point → Point :=
  Projectivization.map (localLinear p M) (local_injective p M hM)

theorem localPoint_one (p : Fin 6) (h : (1 : Matrix2).det ≠ 0) (x : Point) :
    localPoint p 1 h x = x := by
  induction x using Projectivization.ind with | h f hf =>
  simp only [localPoint,Projectivization.map_mk]
  congr 1
  exact local_one p f

theorem localPoint_mul (p : Fin 6) (M N : Matrix2)
    (hM : M.det ≠ 0) (hN : N.det ≠ 0) (hMN : (M*N).det ≠ 0) (x : Point) :
    localPoint p M hM (localPoint p N hN x) = localPoint p (M*N) hMN x := by
  induction x using Projectivization.ind with | h f hf =>
  simp only [localPoint,Projectivization.map_mk]
  congr 1
  exact local_mul p M N f

theorem localPoint_scale (p : Fin 6) (c : ℂ) (M : Matrix2)
    (hM : M.det ≠ 0) (hcM : (c • M).det ≠ 0) (x : Point) :
    localPoint p (c • M) hcM x = localPoint p M hM x := by
  induction x using Projectivization.ind with | h f hf =>
  simp only [localPoint,Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨c,(local_scale_matrix p c M f).symm⟩

def portLinear (e : Equiv.Perm (Fin 6)) : SixTensor →ₗ[ℂ] SixTensor where
  toFun := Tensor.reindex e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem port_injective (e : Equiv.Perm (Fin 6)) : Function.Injective (portLinear e) := by
  intro f g h
  have he := congrArg (Tensor.reindex e.symm) h
  simpa only [portLinear,LinearMap.coe_mk,AddHom.coe_mk,Tensor.reindex_symm] using he

def portPoint (e : Equiv.Perm (Fin 6)) : Point → Point :=
  Projectivization.map (portLinear e) (port_injective e)

def adjacent (p : Fin 5) : Equiv.Perm (Fin 6) := Equiv.swap p.castSucc p.succ

inductive Generator where
  | dress (port : Fin 6) (which : Bool)
  | swap (port : Fin 5)
  deriving DecidableEq, Fintype

def generatorStep : Generator → Point → Point
  | .dress p b => localPoint p (localGenerator b)
      (representative_det_ne_zero .tetrahedral (localGeneratorIndex b))
  | .swap p => portPoint (adjacent p)

/-- Source operations allow all actual tetrahedral directions and all port
permutations. Their matrices are not reduced to formal certificate labels. -/
inductive ActualOperation where
  | dress (port : Fin 6) (matrix : Matrix2) (actual : groupDirection .tetrahedral matrix)
  | permute (permutation : Equiv.Perm (Fin 6))

def actualStep : ActualOperation → Point → Point
  | .dress p M hM => localPoint p M (groupDirection_det_ne_zero .tetrahedral hM)
  | .permute e => portPoint e

def ActualOrbit (base : Point) : Set Point := {x | Generated actualStep base x}

theorem generator_is_actual (g : Generator) (x : Point) :
    Generated actualStep x (generatorStep g x) := by
  cases g with
  | dress p b => exact Generated.next (step := actualStep) (ActualOperation.dress p (localGenerator b)
      (representative_mem .tetrahedral (localGeneratorIndex b))) .base
  | swap p => exact Generated.next (step := actualStep) (ActualOperation.permute (adjacent p)) .base

theorem generator_orbit_subset (base x : Point) :
    Generated generatorStep base x → x ∈ ActualOrbit base :=
  Generated.monotone generator_is_actual

theorem word_generated (p : Fin 6) (w : List Bool) (x : Point) :
    Generated generatorStep x
      (localPoint p (generatorWord w)
        (groupDirection_det_ne_zero .tetrahedral (generatorWord_mem w)) x) := by
  induction w with
  | nil =>
    change Generated generatorStep x (localPoint p 1 _ x)
    rw [localPoint_one]
    exact .base
  | cons b w ih =>
    have he := localPoint_mul p (localGenerator b) (generatorWord w)
      (representative_det_ne_zero .tetrahedral (localGeneratorIndex b))
      (groupDirection_det_ne_zero .tetrahedral (generatorWord_mem w))
      (groupDirection_det_ne_zero .tetrahedral (generatorWord_mem (b::w))) x
    change Generated generatorStep x (localPoint p (localGenerator b * generatorWord w) _ x)
    rw [←he]
    exact Generated.next (Generator.dress p b) ih

theorem local_generated (p : Fin 6) (M : Matrix2)
    (hM : groupDirection .tetrahedral M) (x : Point) :
    Generated generatorStep x (localPoint p M (groupDirection_det_ne_zero .tetrahedral hM) x) := by
  obtain ⟨w,c,hc,rfl⟩ := (tetrahedral_generated M).mp hM
  rw [localPoint_scale p c (generatorWord w)
    (groupDirection_det_ne_zero .tetrahedral (generatorWord_mem w))]
  exact word_generated p w x

theorem portPoint_one (x : Point) : portPoint 1 x = x := by
  induction x using Projectivization.ind with | h f hf =>
  simp only [portPoint,Projectivization.map_mk]
  congr 1

theorem portPoint_mul (e d : Equiv.Perm (Fin 6)) (x : Point) :
    portPoint e (portPoint d x) = portPoint (e*d) x := by
  induction x using Projectivization.ind with | h f hf =>
  simp only [portPoint,Projectivization.map_mk]
  congr 1

theorem permutation_generated (e : Equiv.Perm (Fin 6)) (x : Point) :
    Generated generatorStep x (portPoint e x) := by
  let S : Submonoid (Equiv.Perm (Fin 6)) := {
    carrier := {e | ∀ x, Generated generatorStep x (portPoint e x)}
    one_mem' := by intro x; rw [portPoint_one]; exact .base
    mul_mem' := by
      intro e d he hd x
      rw [←portPoint_mul]
      exact (hd x).trans (he (portPoint d x)) }
  have hg : Set.range (fun p : Fin 5 => Equiv.swap p.castSucc p.succ) ⊆ S := by
    rintro _ ⟨p,rfl⟩ x
    exact Generated.next (Generator.swap p) .base
  have h := Submonoid.closure_le.mpr hg
  have he : e ∈ Submonoid.closure (Set.range (fun p : Fin 5 => Equiv.swap p.castSucc p.succ)) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  exact h he x

theorem actual_is_generated (a : ActualOperation) (x : Point) :
    Generated generatorStep x (actualStep a x) := by
  cases a with
  | dress p M hM => exact local_generated p M hM x
  | permute e => exact permutation_generated e x

/-- Exact identification with the full actual local tetrahedral/permutation
orbit. The small generator set is justified independently of finite candidates. -/
theorem generated_iff_actual (base x : Point) :
    Generated generatorStep base x ↔ x ∈ ActualOrbit base :=
  ⟨generator_orbit_subset base x,Generated.monotone actual_is_generated⟩

end
end Holant.Certificates.TetrahedralEightPort.OrbitActions
