import Holant.Certificates.TetrahedralPreservers.RangeGeometry
import Holant.Certificates.TetrahedralPreservers.ProjectionRaw

/-! Exclusion of ranks two and three for arbitrary complex two-sided
preservers. Finite root geometry is combined with genuine range bases and
the bilinear adjoint identity; there is no matrix-atlas coverage hypothesis. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

@[simp] theorem liftVector_add (u v : ZV) : liftVector (u+v)=liftVector u+liftVector v := by
  ext i; simp [liftVector]
@[simp] theorem liftVector_smul (c : ℤ) (u : ZV) : liftVector (c • u)=(c : ℂ) • liftVector u := by
  ext i; simp [liftVector]
@[simp] theorem liftVector_zero : liftVector 0=0 := by ext i; simp [liftVector]

theorem zPair_lift (u v : ZV) : (zPair u v : ℂ)=pairing (liftVector u) (liftVector v) := by
  simp [zPair,pairing,liftVector,frobeniusSigns,Fin.sum_univ_succ]
  ring

theorem projectedCross_complex (i j r s : Fin 12) : (projectedCross i j r s : ℂ)=
    pairing (standardPoint i) (standardPoint r)*pairing (standardPoint j) (standardPoint s)-
      pairing (standardPoint i) (standardPoint s)*pairing (standardPoint j) (standardPoint r) := by
  simp only [projectedCross,Int.cast_sub,Int.cast_mul,zPair_lift,lift_zstandard]

theorem independent_triple_certificate (u : Fin 3 → Fin 12)
    (hu : LinearIndependent ℂ (fun i => standardPoint (u i))) :
    zDot (tripleNormal (u 0) (u 1) (u 2)) (zstandard (u 0))=0 ∧
    zDot (tripleNormal (u 0) (u 1) (u 2)) (zstandard (u 1))=0 ∧
    zDot (tripleNormal (u 0) (u 1) (u 2)) (zstandard (u 2))=0 ∧
    ((Finset.univ : Finset (Fin 12)).filter (fun r =>
      zDot (tripleNormal (u 0) (u 1) (u 2)) (zstandard r)=0)).card ≤ 6 ∧
    ∀ a b : Fin 7, a ≠ b →
      projectedCross (u 0) (u 1) (tripleWitness (u 0) (u 1) (u 2) a)
        (tripleWitness (u 0) (u 1) (u 2) b) ≠ 0 ∨
      projectedCross (u 0) (u 2) (tripleWitness (u 0) (u 1) (u 2) a)
        (tripleWitness (u 0) (u 1) (u 2) b) ≠ 0 ∨
      projectedCross (u 1) (u 2) (tripleWitness (u 0) (u 1) (u 2) a)
        (tripleWitness (u 0) (u 1) (u 2) b) ≠ 0 := by
  rcases tripleProjection_certificate (u 0) (u 1) (u 2) with ⟨⟨a,ha⟩,hrel⟩ | h
  · have hh := congrArg liftVector hrel
    simp only [liftVector_add,liftVector_smul,liftVector_zero,lift_zstandard] at hh
    let c : Fin 3 → ℂ := fun i => (tripleRelation (u 0) (u 1) (u 2) i : ℂ)
    have hz : ∑ i : Fin 3, c i • standardPoint (u i)=0 := by
      simpa [c,Fin.sum_univ_succ,add_assoc] using hh
    have hzero := (Fintype.linearIndependent_iff.mp hu) c hz a
    exact False.elim (ha (Int.cast_eq_zero.mp hzero))
  · exact h

def normalFunctional (n : ZV) : V →ₗ[ℂ] ℂ where
  toFun r := ∑ i : Fin 4, (n i : ℂ)*r i
  map_add' r s := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' c r := by
    simp [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem zDot_lift (n r : ZV) : (zDot n r : ℂ)=normalFunctional n (liftVector r) := by
  simp [zDot,normalFunctional,liftVector,Fin.sum_univ_succ]
  ring

theorem rootIndices_three_basis_bound (W : Submodule ℂ V) (u : Fin 3 → Fin 12)
    (hu : LinearIndependent ℂ (fun i => standardPoint (u i)))
    (hspan : Submodule.span ℂ (Set.range (fun i => standardPoint (u i)))=W) :
    (rootIndices W).card ≤ 6 := by
  classical
  obtain ⟨h0,h1,h2,hcard,_⟩ := independent_triple_certificate u hu
  let n := tripleNormal (u 0) (u 1) (u 2)
  have hn (i : Fin 3) : normalFunctional n (standardPoint (u i))=0 := by
    rw [← lift_zstandard,← zDot_lift]
    apply Int.cast_eq_zero.mpr
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hW : W ≤ LinearMap.ker (normalFunctional n) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hn i
  have hsub : rootIndices W ⊆ Finset.univ.filter (fun r => zDot n (zstandard r)=0) := by
    intro r hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ r,?_⟩
    have hc : (zDot n (zstandard r) : ℂ)=0 := by
      rw [zDot_lift,lift_zstandard]
      exact hW ((mem_rootIndices W r).mp hr)
    exact Int.cast_eq_zero.mp hc
  exact (Finset.card_le_card hsub).trans hcard

theorem no_standard_rank_two (A : End) (h : TwoSided Standard A) : A.rank ≠ 2 := by
  intro hA
  have hs : (sharp A).rank=2 := by rw [rank_sharp,hA]
  obtain ⟨u,hu,hm,_⟩ := range_root_basis (sharp A) h.2 hs
  have hij : u 0 ≠ u 1 := by
    intro he
    have hh := hu.injective (congrArg standardPoint he)
    norm_num at hh
  have hlo : 4 ≤ (rootIndices (LinearMap.range A.mulVecLin)).card := by
    apply projected_directions_bound A h.1 (by omega : 2 ≤ 4)
      (fun i : Fin 2 => standardPoint (u i)) hm (pairWitness (u 0) (u 1))
    intro a b hab
    refine ⟨0,1,?_⟩
    rw [← projectedCross_complex]
    exact_mod_cast pairProjection_certificate (u 0) (u 1) hij a b hab
  have hhi := rootIndices_two_dimensional_bound (LinearMap.range A.mulVecLin)
    (by change A.rank ≤ 2; omega)
  omega

theorem no_standard_rank_three (A : End) (h : TwoSided Standard A) : A.rank ≠ 3 := by
  intro hA
  have hs : (sharp A).rank=3 := by rw [rank_sharp,hA]
  obtain ⟨u,hu,hm,_⟩ := range_root_basis (sharp A) h.2 hs
  have hc := (independent_triple_certificate u hu).2.2.2.2
  have hlo : 7 ≤ (rootIndices (LinearMap.range A.mulVecLin)).card := by
    apply projected_directions_bound A h.1 (by omega : 2 ≤ 7)
      (fun i : Fin 3 => standardPoint (u i)) hm (tripleWitness (u 0) (u 1) (u 2))
    intro a b hab
    rcases hc a b hab with hh | hh | hh
    · refine ⟨0,1,?_⟩
      rw [← projectedCross_complex]
      exact_mod_cast hh
    · refine ⟨0,2,?_⟩
      rw [← projectedCross_complex]
      exact_mod_cast hh
    · refine ⟨1,2,?_⟩
      rw [← projectedCross_complex]
      exact_mod_cast hh
  obtain ⟨v,hv,_,hspan⟩ := range_root_basis A h.1 hA
  have hhi := rootIndices_three_basis_bound (LinearMap.range A.mulVecLin) v hv hspan
  omega

theorem no_external_rank_two (A : End) (h : TwoSided External A) : A.rank ≠ 2 := by
  have hh := no_standard_rank_two (toStandard A) ((standard_twoSided_iff A).mpr h)
  simpa only [rank_toStandard] using hh

theorem no_external_rank_three (A : End) (h : TwoSided External A) : A.rank ≠ 3 := by
  have hh := no_standard_rank_three (toStandard A) ((standard_twoSided_iff A).mpr h)
  simpa only [rank_toStandard] using hh

end Holant.Certificates.TetrahedralPreservers
