import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankFourGeometry

/-! Generic I/opposite-I coefficient proof extracted from RankFour/Incidence.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Preserver.Completion
open scoped BigOperators Matrix

theorem mulVec_span_pair_iff (A : End) (hd : A.det ≠ 0) (u v w : V) :
    A *ᵥ w ∈ Submodule.span ℂ ({A *ᵥ u,A *ᵥ v} : Set V) ↔
      w ∈ Submodule.span ℂ ({u,v} : Set V) := by
  constructor
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨a,b,?_⟩
    apply Matrix.mulVec_injective_of_det_ne_zero hd
    simpa only [Matrix.mulVec_add,Matrix.mulVec_smul] using he
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨a,b,?_⟩
    simpa only [Matrix.mulVec_add,Matrix.mulVec_smul] using congrArg A.mulVec he

theorem scaled_span_pair_iff (u v w : V) (a b c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    c • w ∈ Submodule.span ℂ ({a • u,b • v} : Set V) ↔
      w ∈ Submodule.span ℂ ({u,v} : Set V) := by
  constructor
  · intro h
    obtain ⟨x,y,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨c⁻¹*x*a,c⁻¹*y*b,?_⟩
    have hh := congrArg (fun z : V => c⁻¹ • z) he
    simpa only [smul_add,smul_smul,inv_mul_cancel₀ hc,one_smul,mul_assoc] using hh
  · intro h
    obtain ⟨x,y,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨c*x*a⁻¹,c*y*b⁻¹,?_⟩
    have hh := congrArg (fun z : V => c • z) he
    simpa only [smul_add,smul_smul,mul_assoc,inv_mul_cancel₀ ha,
      inv_mul_cancel₀ hb,mul_one] using hh


theorem action_incidence (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (σ : Equiv.Perm (Fin 60)) (c : Fin 60 → ℂ) (hc : ∀ i,c i ≠ 0)
    (he : ∀ i,A *ᵥ point opposite i = c i • point opposite (σ i)) (i j k : Fin 60) :
    point opposite (σ k) ∈
        Submodule.span ℂ ({point opposite (σ i),point opposite (σ j)} : Set V) ↔
      point opposite k ∈ Submodule.span ℂ ({point opposite i,point opposite j} : Set V) := by
  have h := mulVec_span_pair_iff A hA
    (point opposite i) (point opposite j) (point opposite k)
  rw [he i,he j,he k] at h
  exact (scaled_span_pair_iff _ _ _ _ _ _
    (hc i) (hc j) (hc k)).symm.trans h

theorem action_secant (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (σ : Equiv.Perm (Fin 60)) (c : Fin 60 → ℂ) (hc : ∀ i,c i ≠ 0)
    (he : ∀ i,A *ᵥ point opposite i = c i • point opposite (σ i)) (i j : Fin 60) :
    (secant opposite i j).map σ.toEmbedding = secant opposite (σ i) (σ j) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hk
    exact (mem_secant _ _ _ _).mpr
      ((action_incidence opposite A hA σ c hc he i j l).mpr
        ((mem_secant _ _ _ _).mp hl))
  · intro hk
    refine Finset.mem_map.mpr ⟨σ.symm k,?_,σ.apply_symm_apply k⟩
    apply (mem_secant _ _ _ _).mpr
    apply (action_incidence opposite A hA σ c hc he i j (σ.symm k)).mp
    simpa only [σ.apply_symm_apply] using (mem_secant _ _ _ _).mp hk

theorem action_secant_card (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (σ : Equiv.Perm (Fin 60)) (c : Fin 60 → ℂ) (hc : ∀ i,c i ≠ 0)
    (he : ∀ i,A *ᵥ point opposite i = c i • point opposite (σ i)) (i j : Fin 60) :
    (secant opposite (σ i) (σ j)).card = (secant opposite i j).card := by
  rw [←action_secant opposite A hA σ c hc he i j,Finset.card_map]

/-- New H4-specific constraint on the actual images, rather than a
promised finite automorphism or a Euclidean/Hermitian surrogate. -/
theorem action_orthogonal (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (σ : Equiv.Perm (Fin 60)) (c : Fin 60 → ℂ) (hc : ∀ i,c i ≠ 0)
    (he : ∀ i,A *ᵥ point opposite i = c i • point opposite (σ i)) (i j : Fin 60)
    (hij : i ≠ j) (hz : rowPolar opposite (point opposite i) (point opposite j)=0) :
    rowPolar opposite (A *ᵥ point opposite i) (A *ᵥ point opposite j)=0 := by
  have hcard := (secant_two_iff_orthogonal opposite i j hij).mpr hz
  have himage : (secant opposite (σ i) (σ j)).card=2 := by
    rw [action_secant_card opposite A hA σ c hc he]
    exact hcard
  have hs : σ i ≠ σ j := fun h => hij (σ.injective h)
  have hzero := (secant_two_iff_orthogonal opposite (σ i) (σ j) hs).mp himage
  rw [he i,he j,rowPolar_smul,hzero,mul_zero]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
end
