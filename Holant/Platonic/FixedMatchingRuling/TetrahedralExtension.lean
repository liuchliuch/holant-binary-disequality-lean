import Holant.Platonic.FixedMatchingRuling.QuadraticInterpolation
import Holant.Certificates.MatchingProductBridge.QuaternionCoordinates

/-! The actual twelve quaternion test matrices force every Segre minor to
vanish on Mat₂, including at zero. -/
namespace Holant.Platonic.FixedMatchingRuling
noncomputable section
open scoped BigOperators
open Module Holant.Certificates.MatchingProductBridge

variable {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
variable {W : M → Type*} [∀e, AddCommGroup (W e)] [∀e, Module ℂ (W e)]
  [∀e, FiniteDimensional ℂ (W e)]

 theorem coordinate_test_extension
    (Φ : (Fin 4→ℂ) →ₗ[ℂ] PiTensorProduct ℂ W)
    (ha : ∀i, Segre.TensorPureOrZero (Φ (axis i)))
    (hs : ∀b, Segre.TensorPureOrZero (Φ (signPoint b))) :
    ∀x, Segre.TensorPureOrZero (Φ x) := by
  classical
  let b := fun e => Module.finBasis ℂ (W e)
  let F := (Segre.tensorCoordinates b).toLinearMap.comp Φ
  intro z
  apply (Segre.tensor_minors_iff b (Φ z)).mp
  intro e x y
  let A := (LinearMap.proj x).comp F
  let B := (LinearMap.proj y).comp F
  let C := (LinearMap.proj (Function.update x e (y e))).comp F
  let D := (LinearMap.proj (Function.update y e (x e))).comp F
  exact minor_vanishes A B C D
    (fun i => (Segre.tensor_minors_iff b (Φ (axis i))).mpr (ha i) e x y)
    (fun a => (Segre.tensor_minors_iff b (Φ (signPoint a))).mpr (hs a) e x y) z

/-- Literal complex-linear quaternion coordinate synthesis in Mat₂. -/
def quaternionLinear : (Fin 4→ℂ) →ₗ[ℂ] Binary where
  toFun x := ∑i : Fin 4,x i • quaternionBasis i
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum,smul_smul]

 theorem quaternionLinear_axis (i : Fin 4) : quaternionLinear (axis i)=quaternionBasis i := by
  simp [quaternionLinear,axis]

 theorem quaternionLinear_signPoint (b : Fin 3→Bool) :
    quaternionLinear (signPoint b)=quaternion ![1,signBit (b 0),signBit (b 1),signBit (b 2)] := by
  ext a c
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    simp [quaternionLinear,signPoint,quaternion,quaternionBasis,signBit,Fin.sum_univ_succ,h0,h1,h2] <;> ring

 theorem quaternionLinear_reconstruction (K : Binary) :
    quaternionLinear (quaternionCoefficient K)=K := by
  ext a b
  cases a <;> cases b <;>
    simp [quaternionLinear,quaternionCoefficient,quaternionBasis,Fin.sum_univ_succ,
      Q0,Q1,Q2,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

 theorem quaternionLinear_surjective : Function.Surjective quaternionLinear :=
  fun K => ⟨quaternionCoefficient K,quaternionLinear_reconstruction K⟩

 theorem tetrahedral_test_extension (Φ : Binary →ₗ[ℂ] PiTensorProduct ℂ W)
    (htest : ∀K,tetrahedralBase K → Segre.TensorPureOrZero (Φ K)) :
    ∀K,Segre.TensorPureOrZero (Φ K) := by
  have he : ∀x,Segre.TensorPureOrZero ((Φ.comp quaternionLinear) x) :=
    coordinate_test_extension (Φ.comp quaternionLinear)
      (by intro i; simpa only [LinearMap.comp_apply,quaternionLinear_axis] using
        htest (quaternionBasis i) (Or.inl ⟨i,rfl⟩))
      (by intro b; simpa only [LinearMap.comp_apply,quaternionLinear_signPoint] using
        htest (quaternion ![1,signBit (b 0),signBit (b 1),signBit (b 2)]) (Or.inr ⟨b,rfl⟩))
  intro K
  obtain ⟨x,rfl⟩ := quaternionLinear_surjective K
  exact he x

/-- Source9.6's linear-space conclusion for the actual quaternion test set,
with arbitrary nonempty finite factors and zero card values permitted. -/
 theorem tetrahedral_fixed_matching_ruling (Φ : Binary →ₗ[ℂ] PiTensorProduct ℂ W)
    (hΦ : Φ≠0)
    (htest : ∀K,tetrahedralBase K → Segre.TensorPureOrZero (Φ K)) :
    ∃(e : M) (U : ∀e,W e) (ψ : Binary →ₗ[ℂ] W e),
      (∀f,f≠e → U f≠0) ∧
      ∀K,Φ K=PiTensorProduct.tprod ℂ (Function.update U e (ψ K)) :=
  Segre.linear_image_ruling Φ hΦ (tetrahedral_test_extension Φ htest)


 theorem tensorPureOrZero_smul (c : ℂ) {t : PiTensorProduct ℂ W}
    (h : Segre.TensorPureOrZero t) : Segre.TensorPureOrZero (c • t) := by
  classical
  rcases h with rfl|⟨U,rfl⟩
  · exact Or.inl (smul_zero _)
  · let e : M := Classical.arbitrary M
    refine Or.inr ⟨Function.update U e (c • U e),?_⟩
    rw [(PiTensorProduct.tprod ℂ).map_update_smul,Function.update_eq_self]

 theorem tensorPureOrZero_smul_iff (c : ℂ) (hc : c≠0) (t : PiTensorProduct ℂ W) :
    Segre.TensorPureOrZero (c • t) ↔ Segre.TensorPureOrZero t := by
  constructor
  · intro h
    have hh := tensorPureOrZero_smul c⁻¹ h
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh
  · exact tensorPureOrZero_smul c

/-- Source projective tests may be supplied with any recorded nonzero scales.
D is an arbitrary set of actual representatives; no finite enumeration,
invertibility restriction, or nonzero image condition is imposed. -/
 theorem source_projective_fixed_matching_ruling
    (D : Set Binary) (Φ : Binary →ₗ[ℂ] PiTensorProduct ℂ W) (hΦ : Φ≠0)
    (hcontains : ∀K,tetrahedralBase K → ∃c : ℂ,c≠0 ∧ c • K∈D)
    (htest : ∀K∈D,Segre.TensorPureOrZero (Φ K)) :
    ∃(e : M) (U : ∀e,W e) (ψ : Binary →ₗ[ℂ] W e),
      (∀f,f≠e → U f≠0) ∧
      ∀K,Φ K=PiTensorProduct.tprod ℂ (Function.update U e (ψ K)) := by
  apply tetrahedral_fixed_matching_ruling Φ hΦ
  intro K hK
  obtain ⟨c,hc,hd⟩ := hcontains K hK
  have hh := htest (c • K) hd
  rw [map_smul] at hh
  exact (tensorPureOrZero_smul_iff c hc (Φ K)).mp hh

end
end Holant.Platonic.FixedMatchingRuling
