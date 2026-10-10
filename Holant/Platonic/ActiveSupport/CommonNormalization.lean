import Holant.Platonic.ActiveSupport.TetrahedralGeometry
import Holant.Platonic.ActiveSupport.SupportShapes

/-! One Clifford, one retained amplitude, and the resulting four supports. -/
namespace Holant.Platonic.ActiveSupport
open Holant Holant.Platonic.StabilizerLine
open Holant.Certificates.MatchingProductBridge
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def TetrahedralAffine (Φ : Binary →ₗ[ℂ] Signature ℂ n) : Prop :=
  ∀K,tetrahedralBase K → ComplexAffine (Φ K)

theorem TetrahedralAffine.direction {Φ : Binary →ₗ[ℂ] Signature ℂ n}
    (hΦ : TetrahedralAffine Φ) {K : Binary} (hK : groupDirection .tetrahedral K) :
    ComplexAffine (Φ K) := by
  obtain ⟨c,hc,V,hV,rfl⟩ := hK
  rw [map_smul]
  exact (hΦ V hV).scale c

theorem TetrahedralAffine.transport {Φ : Binary →ₗ[ℂ] Signature ℂ n}
    (hΦ : TetrahedralAffine Φ) (L : Matrix Bool Bool ℂ)
    (hL : groupDirection .tetrahedral L) : TetrahedralAffine (Φ.comp (leftMultiply L)) := by
  intro K hK
  exact hΦ.direction (leftMultiply_direction L hL ⟨1,one_ne_zero,K,hK,by simp⟩)

theorem TetrahedralAffine.clifford {Φ : Binary →ₗ[ℂ] Signature ℂ n}
    (hΦ : TetrahedralAffine Φ) (C : AnalyticClifford n)
    (hC : ∀f,ComplexAffine f → ComplexAffine (C.operator f)) :
    TetrahedralAffine (C.operator.toLinearMap.comp Φ) := by
  intro K hK
  exact hC _ (hΦ K hK)

def pairedSupports (Φ : Binary →ₗ[ℂ] Signature ℂ n) : Fin 4→Finset (BinaryVector n) :=
  fun j => offSupport (Φ (paired j))

def pairedSupportUnion (Φ : Binary →ₗ[ℂ] Signature ℂ n) : Finset (BinaryVector n) :=
  Finset.univ.biUnion (pairedSupports Φ)

theorem pairedSupports_shape (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (hΦ : TetrahedralAffine Φ) (α : ℂ) (hα : α≠0)
    (hA : Φ anchor=fun x => α*delta x) (j : Fin 4) :
    (pairedSupports Φ j).card≤3 ∧
      ((pairedSupports Φ j).card=3 → ∑x∈pairedSupports Φ j,x=0) := by
  apply normalized_offSupport_shape (Φ anchor) (Φ (paired j)) α hα hA
    (hΦ _ (paired_base j)) (pairSign j) (pairSign_ne_zero j)
  have hh := (hΦ (quaternionBasis j) (Or.inl ⟨j,rfl⟩)).scale (2*pairSign j)
  have he := congrArg Φ (anchor_pair_axis j)
  simp only [map_add,map_smul] at he
  change ComplexAffine (Φ anchor+pairSign j • Φ (paired j))
  rw [he]
  exact hh

theorem paired_relation_values (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (α : ℂ) (hA : Φ anchor=fun x => α*delta x)
    (x : BinaryVector n) (hx : x≠0) :
    -Φ (paired 0) (wordVector x)+Φ (paired 1) (wordVector x)+
      Φ (paired 2) (wordVector x)+Φ (paired 3) (wordVector x)=0 := by
  have he := congrArg (fun K => Φ K (wordVector x)) paired_relation
  simp only [map_smul,map_add,map_neg,Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.neg_apply] at he
  rw [hA] at he
  simp only [delta_vector,ite_eq_right hx,mul_zero] at he
  exact he.symm

theorem pairedSupports_second (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (α : ℂ) (hA : Φ anchor=fun x => α*delta x)
    (j : Fin 4) (x : BinaryVector n) (hx : x∈pairedSupports Φ j) :
    ∃k : Fin 4,k≠j ∧ x∈pairedSupports Φ k := by
  have hx' : x≠0 ∧ Φ (paired j) (wordVector x)≠0 := (mem_offSupport _ _).mp hx
  by_contra hn
  push Not at hn
  have hz (k : Fin 4) (hk : k≠j) : Φ (paired k) (wordVector x)=0 := by
    by_contra hh
    exact hn k hk ((mem_offSupport _ _).mpr ⟨hx'.1,hh⟩)
  have he := paired_relation_values Φ α hA x hx'.1
  apply hx'.2
  fin_cases j
  · have h1 := hz 1 (by decide)
    have h2 := hz 2 (by decide)
    have h3 := hz 3 (by decide)
    simp [h1,h2,h3] at he
    exact he
  · have h0 := hz 0 (by decide)
    have h2 := hz 2 (by decide)
    have h3 := hz 3 (by decide)
    simpa [h0,h2,h3] using he
  · have h0 := hz 0 (by decide)
    have h1 := hz 1 (by decide)
    have h3 := hz 3 (by decide)
    simpa [h0,h1,h3] using he
  · have h0 := hz 0 (by decide)
    have h1 := hz 1 (by decide)
    have h2 := hz 2 (by decide)
    simpa [h0,h1,h2] using he

theorem pairedSupports_double (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (α : ℂ) (hA : Φ anchor=fun x => α*delta x)
    (x : BinaryVector n) (hx : x∈pairedSupportUnion Φ) :
    2≤(Finset.univ.filter (fun j : Fin 4 => x∈pairedSupports Φ j)).card := by
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨k,hkj,hk⟩ := pairedSupports_second Φ α hA j x hj
  have hsub : {j,k}⊆Finset.univ.filter (fun i : Fin 4 => x∈pairedSupports Φ i) := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl <;> simp [hj,hk]
  have hh := Finset.card_le_card hsub
  simpa [Ne.symm hkj] using hh

/-- Exact support containment for every input matrix follows from the proved
four-point reconstruction, including the origin and zero images. -/
theorem support_all_matrices (Φ : Binary →ₗ[ℂ] Signature ℂ n) (K : Binary)
    (x : BinaryVector n) (hx : Φ K (wordVector x)≠0) :
    x∈Submodule.span (ZMod 2) (pairedSupportUnion Φ : Set (BinaryVector n)) := by
  by_cases h0 : x=0
  · subst x
    exact Submodule.zero_mem _
  apply Submodule.subset_span
  by_contra hn
  have hz (j : Fin 4) : Φ (paired j) (wordVector x)=0 := by
    by_contra hh
    apply hn
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,(mem_offSupport _ _).mpr ⟨h0,hh⟩⟩
  apply hx
  rw [←paired_reconstruction K,map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hz,mul_zero,Finset.sum_const_zero]

end
end Holant.Platonic.ActiveSupport
