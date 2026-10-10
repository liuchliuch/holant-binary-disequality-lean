import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralIncidence

/-! Coefficient extraction from the preserved marked-octahedral proof. The finite root permutation determines the complex
operator up to one nonzero scalar. This uses four genuine chart axes and
the genuine all-signs-positive root, rather than a promised finite list of
maps. Consequently arbitrary rank-four projective preservers inject into
Fin 24 permutations. The sharper 1152 count is NOT proved here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open scoped BigOperators Matrix

/-- Only an analytic coefficient chart for the already fixed marked row. -/
def thetaLinearEquiv (f : Form) : BinaryMatrix ≃ₗ[ℂ] BinaryMatrix where
  toFun := complexTheta f
  invFun := complexPull f
  left_inv := complexPull_complexTheta f
  right_inv := complexTheta_complexPull f
  map_add' U V := by simp [complexTheta,Matrix.mul_add,Matrix.add_mul]
  map_smul' c U := complexTheta_smul f c U

def chart (f : Form) : V ≃ₗ[ℂ] V :=
  (coordinates.symm.trans (thetaLinearEquiv f)).trans coordinates

def axis (i : Fin 4) : Fin 24 := ⟨i.val,by omega⟩

theorem point_chart (f : Form) (k : Fin 24) :
    point f k = chart f (coordinates (complexMatrix (OctahedralSeparator.standard k))) := by
  simp only [point,kernel,complexMatrix_theta]
  change coordinates (complexTheta f (complexMatrix (OctahedralSeparator.standard k))) =
    coordinates (complexTheta f (coordinates.symm
      (coordinates (complexMatrix (OctahedralSeparator.standard k)))))
  rw [coordinates.symm_apply_apply]

theorem point_axis (f : Form) (i : Fin 4) :
    point f (axis i) = chart f (Pi.single i 1) := by
  have hs : OctahedralSeparator.standard (axis i) = OctahedralSeparator.q i := by
    fin_cases i <;> rfl
  rw [point_chart,hs,complexMatrix_q,coordinates_basis]

/-- Entry four is the existing q0+q1+q2+q3 root, not a new vector. -/
theorem point_sum (f : Form) : point f (4 : Fin 24) =
    ∑ i : Fin 4, point f (axis i) := by
  have hs : OctahedralSeparator.standard (4 : Fin 24) =
      OctahedralSeparator.q 0+OctahedralSeparator.q 1+
        OctahedralSeparator.q 2+OctahedralSeparator.q 3 := by
    funext a b
    simp [OctahedralSeparator.standard,signed,signs,ms]
  have hq (i : Fin 4) : coordinates (complexMatrix (OctahedralSeparator.q i))=Pi.single i 1 := by
    rw [complexMatrix_q,coordinates_basis]
  have hsum : (∑i : Fin 4,Pi.single i (1 : ℂ))=
      Pi.single 0 1+Pi.single 1 1+Pi.single 2 1+Pi.single 3 1 := by
    simp [Fin.sum_univ_succ,add_assoc]
  have hc : coordinates (complexMatrix (OctahedralSeparator.standard (4 : Fin 24)))=
      ∑i : Fin 4,Pi.single i (1 : ℂ) := by
    rw [hs,hsum]
    simp only [complexMatrix_add,map_add,hq]
  rw [point_chart,hc,map_sum]
  simp only [←point_axis]

theorem root_expansion (f : Form) (v : V) :
    v = ∑ i : Fin 4, (chart f).symm v i • point f (axis i) := by
  have hs : (∑ i : Fin 4, (chart f).symm v i • Pi.single i (1 : ℂ)) =
      (chart f).symm v := by
    ext j
    simp [Pi.single_apply]
  calc
    v = chart f ((chart f).symm v) := ((chart f).apply_symm_apply v).symm
    _ = chart f (∑ i : Fin 4, (chart f).symm v i • Pi.single i (1 : ℂ)) :=
      congrArg (chart f) hs.symm
    _ = _ := by simp only [map_sum,map_smul,←point_axis]

private theorem expansion_images (f : Form) (A : End) (v : V) :
    A *ᵥ v = ∑ i : Fin 4, (chart f).symm v i • (A *ᵥ point f (axis i)) := by
  calc
    A *ᵥ v = A.mulVecLin (∑ i : Fin 4, (chart f).symm v i • point f (axis i)) :=
      congrArg A.mulVecLin (root_expansion f v)
    _ = _ := by simp only [map_sum,map_smul,Matrix.mulVecLin_apply]

/-- This is arbitrary-map coverage: equal finite permutations force equal
projective operators. No normal form of either map is an input. -/
theorem same_permutation_proportional (f : Form) (A B : End)
    (hd : B.det ≠ 0) (p : RootAction f A) (q : RootAction f B)
    (he : p.perm = q.perm) : ∃ c : ℂ, c ≠ 0 ∧ A = c • B := by
  let d : Fin 24 → ℂ := fun i => p.scale i*(q.scale i)⁻¹
  have hdscale (i : Fin 24) : d i ≠ 0 :=
    mul_ne_zero (p.scale_ne_zero i) (inv_ne_zero (q.scale_ne_zero i))
  have images (i : Fin 24) : A *ᵥ point f i = d i • (B *ᵥ point f i) := by
    rw [p.image_eq,q.image_eq,he,smul_smul]
    simp only [d,mul_assoc,inv_mul_cancel₀ (q.scale_ne_zero i),mul_one]
  have sum_eq : (∑ i : Fin 4, d (axis i) • point f (axis i)) =
      d 4 • point f (4 : Fin 24) := by
    apply Matrix.mulVec_injective_of_det_ne_zero hd
    change B.mulVecLin (∑ i : Fin 4, d (axis i) • point f (axis i)) =
      B.mulVecLin (d 4 • point f (4 : Fin 24))
    simp only [map_sum,map_smul,Matrix.mulVecLin_apply]
    calc
      (∑ i : Fin 4, d (axis i) • (B *ᵥ point f (axis i))) =
          ∑ i : Fin 4, A *ᵥ point f (axis i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (images (axis i)).symm
      _ = A *ᵥ point f (4 : Fin 24) := by
        rw [point_sum]
        simpa only [Matrix.mulVecLin_apply] using
          (map_sum A.mulVecLin (fun i : Fin 4 => point f (axis i)) Finset.univ).symm
      _ = _ := images 4
  have constant (i : Fin 4) : d (axis i) = d 4 := by
    have hh := congrArg (fun v : V => (chart f).symm v i) sum_eq
    rw [point_sum] at hh
    simpa [point_axis,map_sum,map_smul,Pi.single_apply] using hh
  refine ⟨d 4,hdscale 4,?_⟩
  apply matrix_ext_action
  intro v
  rw [Matrix.smul_mulVec,expansion_images f A v,expansion_images f B v,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [images,constant]
  simp only [smul_smul]
  congr 1
  ring

private def classRepresentative (f : Form) (p : RankFourClass (Roots f)) :
    {A : End // ∃ hn : A ≠ 0,
      A.rank = 4 ∧ TwoSided (Roots f) A ∧ p.val = Projectivization.mk ℂ A hn} :=
  ⟨Classical.choose p.property,Classical.choose_spec p.property⟩

private theorem representative_rank (f : Form) (p : RankFourClass (Roots f)) :
    (classRepresentative f p).val.rank = 4 := by
  obtain ⟨hn,hr,hp,he⟩ := (classRepresentative f p).property
  exact hr

private theorem representative_safe (f : Form) (p : RankFourClass (Roots f)) :
    TwoSided (Roots f) (classRepresentative f p).val := by
  obtain ⟨hn,hr,hp,he⟩ := (classRepresentative f p).property
  exact hp

private def classAction (f : Form) (p : RankFourClass (Roots f)) :
    RootAction f (classRepresentative f p).val :=
  rootAction f _ ((rank_four_iff_det_ne_zero _).mp (representative_rank f p))
    (representative_safe f p).1

def classPermutation (f : Form) (p : RankFourClass (Roots f)) : Equiv.Perm (Fin 24) :=
  (classAction f p).perm

theorem classPermutation_incidence (f : Form) (p : RankFourClass (Roots f)) :
    ∀ i j k : Fin 24,
      point f (classPermutation f p k) ∈ Submodule.span ℂ
        ({point f (classPermutation f p i),point f (classPermutation f p j)} : Set V) ↔
      point f k ∈ Submodule.span ℂ ({point f i,point f j} : Set V) :=
  (classAction f p).incidence
    ((rank_four_iff_det_ne_zero _).mp (representative_rank f p))

theorem classPermutation_injective (f : Form) : Function.Injective (classPermutation f) := by
  intro p q he
  obtain ⟨hn,hr,hp,ep⟩ := (classRepresentative f p).property
  obtain ⟨kn,kr,kp,eq⟩ := (classRepresentative f q).property
  obtain ⟨c,hc,hm⟩ := same_permutation_proportional f
    (classRepresentative f p).val (classRepresentative f q).val
    ((rank_four_iff_det_ne_zero _).mp kr) (classAction f p) (classAction f q) he
  apply Subtype.ext
  rw [ep,eq]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,hm.symm⟩

/-- A genuine finite bound for all complex projective rank-four maps.
It deliberately does not assert the manuscript's exact 1152 count. -/
theorem finite_rankFourClass (f : Form) : Finite (RankFourClass (Roots f)) :=
  Finite.of_injective (classPermutation f) (classPermutation_injective f)

theorem rankFourClass_bound (f : Form) :
    Nat.card (RankFourClass (Roots f)) ≤ Nat.factorial 24 := by
  have hh := Nat.card_le_card_of_injective (classPermutation f) (classPermutation_injective f)
  simpa only [Nat.card_perm,Nat.card_fin] using hh

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
