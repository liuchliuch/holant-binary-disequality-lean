import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralDictionary

/-! Coefficient extraction from the preserved marked-octahedral proof. Arbitrary F4 identity stabilizers really are the
48 signed quaternion-axis permutations. The critical new step excludes
diagonal-root axis images using the actual plus/minus root equations;
four-point secant incidence alone is not assumed to distinguish them. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open scoped BigOperators Matrix

/-- Harmonic four-point-line constraint from the actual linear action.
The purported image is a local contradiction branch, never source input. -/
theorem no_diagonal_axis_image (A : End) (h : OneSided (Roots 0) A)
    (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1)
    (i j : Fin 3) (b : Bool) (c : ℂ) (hc : c ≠ 0) :
    A *ᵥ Pi.single i.succ 1 ≠ c •
      (Pi.single (0 : Fin 4) 1 + (signBit b : ℂ) • Pi.single j.succ 1) := by
  intro he
  let vp : V := A *ᵥ point 0 (plus i)
  let vm : V := A *ᵥ point 0 (minus i)
  have hsign : (signBit b : ℂ) ≠ 0 := by cases b <;> norm_num [signBit]
  have vp_zero : vp 0 = 1+c := by
    simp [vp,point_plus,Matrix.mulVec_add,h0,he,Pi.single_apply,
      Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero j),smul_add,smul_smul]
  have vp_other : vp j.succ = c*(signBit b : ℂ) := by
    simp [vp,point_plus,Matrix.mulVec_add,h0,he,Pi.single_apply,
      Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero j),smul_add,smul_smul]
  have vm_zero : vm 0 = 1-c := by
    simp [vm,point_minus,Matrix.mulVec_sub,h0,he,Pi.single_apply,
      Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero j),smul_add,smul_smul]
  have vm_other : vm j.succ = -(c*(signBit b : ℂ)) := by
    simp [vm,point_minus,Matrix.mulVec_sub,h0,he,Pi.single_apply,
      Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero j),smul_add,smul_smul]
  have hpn : vp j.succ ≠ 0 := by rw [vp_other]; exact mul_ne_zero hc hsign
  have hmn : vm j.succ ≠ 0 := by rw [vm_other]; exact neg_ne_zero.mpr (mul_ne_zero hc hsign)
  have hp : vp ∈ Roots 0 := by
    rcases h _ (point_mem 0 (plus i)) with hz | hm
    · exact False.elim (hpn (congrFun hz j.succ))
    · exact hm
  have hm : vm ∈ Roots 0 := by
    rcases h _ (point_mem 0 (minus i)) with hz | hm
    · exact False.elim (hmn (congrFun hz j.succ))
    · exact hm
  have xp := root_coordinate_alternatives hp j hpn
  have xm := root_coordinate_alternatives hm j hmn
  rw [vp_zero,vp_other] at xp
  rw [vm_zero,vm_other] at xm
  cases b <;> simp only [signBit,Bool.false_eq_true,↓reduceIte,
    Complex.ofReal_neg,Complex.ofReal_one,mul_neg,mul_one,neg_neg] at xp xm
  all_goals rcases xp with xp | xp | xp <;> rcases xm with xm | xm | xm
  all_goals first
    | exact one_ne_zero (show (1 : ℂ) = 0 by linear_combination xp)
    | exact one_ne_zero (show (1 : ℂ) = 0 by linear_combination xm)
    | exact one_ne_zero (show (1 : ℂ) = 0 by linear_combination (xp+xm)/2)
    | exact one_ne_zero (show (1 : ℂ) = 0 by linear_combination (2*xp+xm)/3)
    | exact one_ne_zero (show (1 : ℂ) = 0 by linear_combination (xp+2*xm)/3)

/-- Full arbitrary-map stabilizer coverage: the three input axes must
have genuine axis images, not the six diagonal points on rich secants. -/
theorem fixed_identity_axes (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots 0) A)
    (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) (i : Fin 3) :
    ∃ j : Fin 3, ∃ c : ℂ, c ≠ 0 ∧
      A *ᵥ Pi.single i.succ 1 = c • Pi.single j.succ 1 := by
  let p := rootAction 0 A hd h
  have hz : point 0 (0 : Fin 24) = Pi.single (0 : Fin 4) 1 := point_zero_axis 0
  have hs : point 0 (axis i.succ) = Pi.single i.succ 1 := point_zero_axis i.succ
  have pzero : p.perm 0 = 0 := by
    apply point_projectively_injective 0 (p.perm 0) 0 (p.scale 0)⁻¹
    calc
      point 0 (p.perm 0) = (p.scale 0)⁻¹ • (A *ᵥ point 0 0) := by
        rw [p.image_eq,smul_smul,inv_mul_cancel₀ (p.scale_ne_zero 0),one_smul]
      _ = _ := by rw [hz,h0,←hz]
  have hai : axis i.succ ≠ (0 : Fin 24) := by
    intro he
    have hv := congrArg Fin.val he
    change i.val+1 = 0 at hv
    omega
  have hk : p.perm (axis i.succ) ≠ 0 := by
    intro he
    exact hai (p.perm.injective (he.trans pzero.symm))
  have hcard : (baseSecant .octahedral (p.perm (axis i.succ))).card = 4 := by
    calc
      (baseSecant .octahedral (p.perm (axis i.succ))).card =
          (secant 0 0 (p.perm (axis i.succ))).card :=
        congrArg Finset.card (actual_baseSecant _ hk).symm
      _ = (secant 0 (p.perm 0) (p.perm (axis i.succ))).card := by rw [pzero]
      _ = (secant 0 0 (axis i.succ)).card := p.secant_card hd 0 (axis i.succ)
      _ = (baseSecant .octahedral (axis i.succ)).card :=
        congrArg Finset.card (actual_baseSecant _ hai)
      _ = 4 := axis_secant_card i
  have image := p.image_eq (axis i.succ)
  rw [hs] at image
  rcases rich_four_indices _ hk hcard with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨j,hj⟩
  · rw [hj,point_zero_axis] at image
    exact ⟨j,p.scale _,p.scale_ne_zero _,image⟩
  · rw [hj,point_plus] at image
    exact False.elim (no_diagonal_axis_image A h h0 i j false (p.scale _)
      (p.scale_ne_zero _) (by simpa [signBit] using image))
  · rw [hj,point_minus] at image
    exact False.elim (no_diagonal_axis_image A h h0 i j true (p.scale _)
      (p.scale_ne_zero _) (by simpa [signBit,sub_eq_add_neg] using image))

theorem fixed_identity_axis_permutation (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots 0) A)
    (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ c : Fin 3 → ℂ, (∀ i, c i ≠ 0) ∧
      ∀ i, A *ᵥ Pi.single i.succ 1 = c i • Pi.single (σ i).succ 1 := by
  choose σ c hc he using fixed_identity_axes A hd h h0
  have hi := Matrix.mulVec_injective_of_det_ne_zero hd
  have hσ : Function.Injective σ := by
    intro i j hij
    have hh : A *ᵥ Pi.single i.succ 1 = (c i*(c j)⁻¹) • (A *ᵥ Pi.single j.succ 1) := by
      rw [he i,he j,hij,smul_smul]
      congr 1
      field_simp [hc j]
    rw [←Matrix.mulVec_smul] at hh
    have hp := hi hh
    by_contra hn
    have hs : i.succ ≠ j.succ := fun he => hn (Fin.succ_inj.mp he)
    have heq := congrFun hp i.succ
    simp [Pi.single_apply,hs,Ne.symm hs] at heq
  exact ⟨Equiv.ofBijective σ ⟨hσ,Finite.surjective_of_injective hσ⟩,c,hc,he⟩

theorem fixed_identity_signed_columns (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots 0) A)
    (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ ε : Fin 3 → Bool,
      ∀ i, A *ᵥ Pi.single i.succ 1 = (signBit (ε i) : ℂ) • Pi.single (σ i).succ 1 := by
  obtain ⟨σ,c,hc,he⟩ := fixed_identity_axis_permutation A hd h h0
  have hcol0 (j : Fin 4) : A j 0 = (Pi.single (0 : Fin 4) (1 : ℂ) : V) j := by
    simpa using congrFun h0 j
  have hcol (j : Fin 4) (i : Fin 3) :
      A j i.succ = c i*(Pi.single (σ i).succ (1 : ℂ) : V) j := by
    simpa using congrFun (he i) j
  let w : V := A *ᵥ (fun _ => 1)
  have hw0 : w 0 = 1 := by
    change (∑ j : Fin 4, A 0 j*1) = 1
    simp only [mul_one]
    rw [Fin.sum_univ_succ,hcol0]
    simp_rw [hcol]
    simp [Pi.single_apply,Fin.succ_ne_zero]
  have hw (i : Fin 3) : w (σ i).succ = c i := by
    change (∑ j : Fin 4, A (σ i).succ j*1) = c i
    simp only [mul_one]
    rw [Fin.sum_univ_succ,hcol0]
    simp_rw [hcol]
    simp [Pi.single_apply,Fin.succ_ne_zero]
  have hones : (fun _ : Fin 4 => (1 : ℂ)) ∈ Roots 0 := by
    convert point_mem 0 (4 : Fin 24) using 1
    rw [point_zero_table]
    ext i
    fin_cases i <;> norm_num [liftVector,zOcta]
  have hwR : w ∈ Roots 0 := by
    rcases h _ hones with hz | hm
    · exact False.elim (one_ne_zero (hw0.symm.trans (congrFun hz 0)))
    · exact hm
  have signs (i : Fin 3) : ∃ ε : Bool, c i = (signBit ε : ℂ) := by
    have hh := root_coordinate_alternatives hwR (σ i) (by rw [hw]; exact hc i)
    rw [hw0,hw] at hh
    rcases hh with hz | hp | hm
    · exact False.elim (one_ne_zero hz)
    · exact ⟨false,by simpa [signBit] using hp.symm⟩
    · exact ⟨true,by simpa [signBit] using
        (neg_eq_iff_eq_neg.mp hm.symm)⟩
  choose ε hε using signs
  exact ⟨σ,ε,fun i => by rw [he i,hε i]⟩

theorem fixed_identity_complete (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots 0) A)
    (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ ε : Fin 3 → Bool, A = signedMap σ ε := by
  obtain ⟨σ,ε,he⟩ := fixed_identity_signed_columns A hd h h0
  refine ⟨σ,ε,?_⟩
  ext i j
  have hcol : A *ᵥ Pi.single j 1 = signedMap σ ε *ᵥ Pi.single j 1 := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [h0,signedMap_first]
    · rw [he,signedMap_axis]
  simpa using congrFun hcol i

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
