import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTensorTransport
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralFrames

/-! Coefficient extraction from the preserved marked-octahedral proof. Inverse image and J-dual actions are produced from
the ORIGINAL O multiplication table. Exact inverses below are proof
operators only: physical vertices are old representatives at inverse root
indices, with old native-X wires and reverse bits. The marked-frame sharp
producer is consumed from the returned root-owned Frames/Standard source.
No analytic frame is installed as a resource. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
open Holant Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.PlatonicIncidence
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.QuotientEnumeration RankTwo.HarmonicProjectivities
open RankFour.ExactAutomorphisms RankFour.TwoSidedCompleteness
open scoped Matrix BigOperators

def inverseIndex : Fin 24 → Fin 24 :=
  ![0,1,2,3,11,10,9,8,7,6,5,4,13,12,15,14,17,16,18,19,20,21,22,23]

def inverseScale (k : Fin 24) : Scalar := (Products.productScale k (inverseIndex k))⁻¹

theorem finite_inverse : ∀ k : Fin 24,
    Products.productIndex k (inverseIndex k) = 0 ∧
    Products.productIndex (inverseIndex k) k = 0 ∧
    Products.productScale (inverseIndex k) k = Products.productScale k (inverseIndex k) := by
  intro k
  fin_cases k <;> decide +kernel

noncomputable section

private theorem rankThree_point_agree (f : Form) (k : Fin 24) :
    RankThree.point f k=point f k := rfl

theorem kernel_zero (f : Form) : kernel f 0 = 1 := by
  have h : theta f (OctahedralSeparator.standard 0) = q 0 := by
    change mm (inverseConjugator f) (mm (q 0) (conjugator f)) = q 0
    rw [q0_mm,(conjugator_inverses f).2]
  rw [kernel,h,complexMatrix_q0]

def inverseKernel (f : Form) (k : Fin 24) : BinaryMatrix :=
  embed (inverseScale k) • kernel f (inverseIndex k)

theorem inverseScale_ne (k : Fin 24) : embed (inverseScale k) ≠ 0 :=
  embed_ne_zero (inv_ne_zero (Products.productScale_nonzero k (inverseIndex k)))

theorem inverseKernel_right (f : Form) (k : Fin 24) : kernel f k * inverseKernel f k = 1 := by
  rw [inverseKernel,Matrix.mul_smul,kernel_product,(finite_inverse k).1,kernel_zero,smul_smul]
  simp only [inverseScale,embed_inv,inv_mul_cancel₀
    (embed_ne_zero (Products.productScale_nonzero k (inverseIndex k))),one_smul]

theorem inverseKernel_left (f : Form) (k : Fin 24) : inverseKernel f k * kernel f k = 1 := by
  rw [inverseKernel,Matrix.smul_mul,kernel_product,(finite_inverse k).2.1,
    (finite_inverse k).2.2,kernel_zero,smul_smul]
  simp only [inverseScale,embed_inv,inv_mul_cancel₀
    (embed_ne_zero (Products.productScale_nonzero k (inverseIndex k))),one_smul]

theorem inverseKernel_eq (f : Form) (k : Fin 24) : inverseKernel f k = (kernel f k)⁻¹ :=
  (Matrix.inv_eq_right_inv (inverseKernel_right f k)).symm

def inverseOrbit (f : Form) (t : Fin 122) : End :=
  sandwich (inverseKernel f (orbitPair t).1) (inverseKernel f (orbitPair t).2)

theorem inverseOrbit_left (f : Form) (t : Fin 122) :
    inverseOrbit f t * orbitSandwich f t = 1 := by
  rw [inverseOrbit,orbitSandwich,sandwich_comp,inverseKernel_left,inverseKernel_right,sandwich_one]

theorem inverseOrbit_right (f : Form) (t : Fin 122) :
    orbitSandwich f t * inverseOrbit f t = 1 := by
  rw [inverseOrbit,orbitSandwich,sandwich_comp,inverseKernel_right,inverseKernel_left,sandwich_one]

theorem inverseKernel_chart (f : Form) (k : Fin 24) :
    inverseKernel f k = (rowMatrix f)⁻¹ * inverseKernel 0 k * rowMatrix f := by
  simp only [inverseKernel,kernel,theta_zero,complexMatrix_theta,complexTheta,rowMatrix,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]

theorem inverseOrbit_chart (f : Form) (t : Fin 122) :
    inverseOrbit f t = chartMatrix f * inverseOrbit 0 t * inverseChartMatrix f := by
  rw [inverseOrbit,inverseKernel_chart f (orbitPair t).1,
    inverseKernel_chart f (orbitPair t).2,chartMatrix,inverseChartMatrix,
    inverseOrbit,sandwich_comp,sandwich_comp]
  simp only [Matrix.mul_assoc]

/-- All four marked J conditions are produced by the old Gram-corrected
conjugate_twoSided theorem. No orthogonality assumption is inserted. -/
theorem inverseOrbit_twoSided (f : Form) (t : Fin 122) : TwoSided (Roots f) (inverseOrbit f t) := by
  rw [inverseOrbit_chart]
  apply conjugate_twoSided
  apply sandwich_twoSided_zero
  · exact (Direction.standard 0 _).smul (inverseScale_ne _)
  · exact (Direction.standard 0 _).smul (inverseScale_ne _)

def normalizedMap (f : Form) (A : End) (l r : Fin 122) : End :=
  inverseOrbit f l * A * sharp (inverseOrbit f r)

theorem normalized_sharp (f : Form) (A : End) (l r : Fin 122) :
    sharp (normalizedMap f A l r) = normalizedMap f (sharp A) r l := by
  simp only [normalizedMap,sharp_mul,sharp_sharp,Matrix.mul_assoc]

theorem normalized_twoSided (f : Form) (A : End) (l r : Fin 122)
    (h : TwoSided (Roots f) A) : TwoSided (Roots f) (normalizedMap f A l r) := by
  have hg := inverseOrbit_twoSided f r
  have hs : TwoSided (Roots f) (sharp (inverseOrbit f r)) :=
    ⟨hg.2,by simpa only [sharp_sharp] using hg.1⟩
  exact twoSided_comp (twoSided_comp (inverseOrbit_twoSided f l) h) hs

/-- Original basis-plane membership, with the old canonical endpoint
indices. The proof uses the previous line data, not a new line atlas. -/
theorem point_line_plane (f : Form) (t : FourLineCode) (k : Fin 24)
    (hk : k ∈ globalLine .octahedral t.val) :
    point f k ∈ RankTwo.rootPlane f (canonicalPair t.val) := by
  have h := (finite_line_data t.val t.property).2.2.1 f k hk
  have hh := congrArg RankThree.lift h
  rw [RankThree.lift_point,RankThree.lift_add,RankThree.lift_smul,
    RankThree.lift_smul,RankThree.lift_point,RankThree.lift_point] at hh
  simp only [rankThree_point_agree] at hh
  rw [hh]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩))

def baseCode : FourLineCode := ⟨baseLine,baseLine_mem⟩

theorem inverse_point_plane (f : Form) (t : FourLineCode) (k : Fin 24)
    (hk : k ∈ globalLine .octahedral t.val) :
    inverseOrbit f t.val *ᵥ point f k ∈ RankTwo.rootPlane f (canonicalPair baseLine) := by
  obtain ⟨r,hr,he,ha,hc⟩ := (actual_line_orbit f t.val t.property).2 k hk
  change Fin 24 at r
  have h := congrArg (fun v => inverseOrbit f t.val *ᵥ v) ha
  change inverseOrbit f t.val *ᵥ (orbitSandwich f t.val *ᵥ point f r) =
    inverseOrbit f t.val *ᵥ (embed (movedScale (orbitPair t.val).1 (orbitPair t.val).2 r) • point f k) at h
  rw [Matrix.mulVec_mulVec,inverseOrbit_left,Matrix.one_mulVec,Matrix.mulVec_smul] at h
  have he' : inverseOrbit f t.val *ᵥ point f k =
      (embed (movedScale (orbitPair t.val).1 (orbitPair t.val).2 r))⁻¹ • point f r := by
    rw [h,smul_smul,inv_mul_cancel₀ hc,one_smul]
  rw [he']
  exact Submodule.smul_mem _ _ (point_line_plane f baseCode r hr)

theorem paired_sharp (f : Form) (A : End) (l r : FourLineCode) (h : PairedRanges f A l r) :
    PairedRanges f (sharp A) r l := by
  have ht := (twoSided_iff_equations f A).mpr h.polynomials
  refine ⟨h.right,?_,h.rightPair,?_,h.rightSpan,?_,?_,?_⟩
  · simpa only [sharp_sharp] using h.left
  · simpa only [sharp_sharp] using h.leftPair
  · simpa only [sharp_sharp] using h.leftSpan
  · exact (twoSided_iff_equations f _).mp ⟨ht.2,by simpa only [sharp_sharp] using ht.1⟩
  · simpa only [rank_sharp] using h.rank

theorem normalized_range (f : Form) (A : End) (l r : FourLineCode) (h : PairedRanges f A l r) :
    LinearMap.range (normalizedMap f A l.val r.val).mulVecLin =
      RankTwo.rootPlane f (canonicalPair baseLine) := by
  apply le_antisymm
  · rintro v ⟨w,rfl⟩
    have hv : A *ᵥ (sharp (inverseOrbit f r.val) *ᵥ w) ∈
        RankTwo.rootPlane f (canonicalPair l.val) := by
      rw [h.leftSpan]
      exact ⟨_,rfl⟩
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
    change normalizedMap f A l.val r.val *ᵥ w ∈ _
    simp only [normalizedMap,←Matrix.mulVec_mulVec]
    rw [←hc,Fin.sum_univ_two,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (inverse_point_plane f l _ (canonicalPair_mem l.val 0)))
      (Submodule.smul_mem _ _ (inverse_point_plane f l _ (canonicalPair_mem l.val 1)))
  · apply Submodule.span_le.mpr
    rintro v ⟨a,rfl⟩
    let k := canonicalPair baseLine a
    have hk : movedIndex (orbitPair l.val).1 (orbitPair l.val).2 k ∈
        globalLine .octahedral l.val :=
      (actual_line_orbit f l.val l.property).1 k (canonicalPair_mem baseLine a)
    have hs : point f (movedIndex (orbitPair l.val).1 (orbitPair l.val).2 k) ∈
        LinearMap.range A.mulVecLin := by
      rw [←h.left] at hk
      exact (RankTwo.mem_rootIndices f _ _).mp hk
    have hg : orbitSandwich f l.val *ᵥ point f k ∈ LinearMap.range A.mulVecLin := by
      rw [orbitSandwich,moved_point]
      exact Submodule.smul_mem _ _ hs
    obtain ⟨w,hw⟩ := hg
    change A *ᵥ w=orbitSandwich f l.val *ᵥ point f k at hw
    have hz : sharp (inverseOrbit f r.val) *ᵥ (sharp (orbitSandwich f r.val) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec,←sharp_mul,inverseOrbit_right,sharp_one,Matrix.one_mulVec]
    refine ⟨sharp (orbitSandwich f r.val) *ᵥ w,?_⟩
    change normalizedMap f A l.val r.val *ᵥ (sharp (orbitSandwich f r.val) *ᵥ w) = _
    simp only [normalizedMap,←Matrix.mulVec_mulVec]
    rw [hz,hw,Matrix.mulVec_mulVec,inverseOrbit_left,Matrix.one_mulVec]

theorem normalized_dual_range (f : Form) (A : End) (l r : FourLineCode) (h : PairedRanges f A l r) :
    LinearMap.range (sharp (normalizedMap f A l.val r.val)).mulVecLin =
      RankTwo.rootPlane f (canonicalPair baseLine) := by
  rw [normalized_sharp]
  exact normalized_range f (sharp A) r l (paired_sharp f A l r h)

/-- Exact old-line dictionary for the same marked coefficient plane. -/
theorem plane_root_indices (f : Form) (t : Fin 122) :
    RankTwo.rootIndices f (RankTwo.rootPlane f (canonicalPair t)) = globalLine .octahedral t := by
  classical
  have hs : RankTwo.rootPlane f (canonicalPair t) = Submodule.span ℂ
      ({point f (canonicalPair t 0),point f (canonicalPair t 1)} : Set V) := by
    unfold RankTwo.rootPlane
    congr 1
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|h)
      · exact ⟨0,rfl⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp h).symm⟩
  have hm : (RankTwo.rootPlane f (canonicalPair t)).map (RankTwo.coefficientPull f) =
      Submodule.span ℂ ({Holant.Certificates.RainbowOrbit.representative .octahedral (canonicalPair t 0),
        Holant.Certificates.RainbowOrbit.representative .octahedral (canonicalPair t 1)} : Set PlatonicIncidence.Mat) := by
    rw [hs,←Submodule.span_image]
    simp only [Set.image_insert_eq,Set.image_singleton,RankTwo.coefficientPull_point]
  rw [RankTwo.rootIndices_pull,hm]
  ext k
  rw [mem_deletion,globalLine_eq_translated]
  simpa only [canonicalPair,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (translatedLine_iff .octahedral (globalWitness .octahedral t).1 k
      (globalWitness .octahedral t).2).symm

theorem normalized_paired (f : Form) (A : End) (l r : FourLineCode) (h : PairedRanges f A l r) :
    PairedRanges f (normalizedMap f A l.val r.val) baseCode baseCode := by
  have hl := normalized_range f A l r h
  have hr := normalized_dual_range f A l r h
  have ht := normalized_twoSided f A l.val r.val ((twoSided_iff_equations f A).mpr h.polynomials)
  have hi : RankTwo.rootIndices f (LinearMap.range (normalizedMap f A l.val r.val).mulVecLin) =
      globalLine .octahedral baseLine := by rw [hl,plane_root_indices]
  have hj : RankTwo.rootIndices f
      (LinearMap.range (sharp (normalizedMap f A l.val r.val)).mulVecLin) =
      globalLine .octahedral baseLine := by rw [hr,plane_root_indices]
  refine ⟨hi,hj,canonicalPair_range f _ baseLine hi,canonicalPair_range f _ baseLine hj,
    hl.symm,hr.symm,(twoSided_iff_equations f _).mp ht,?_⟩
  change Module.finrank ℂ (LinearMap.range (normalizedMap f A l.val r.val).mulVecLin) = 2
  rw [hl]
  exact canonicalPair_finrank f baseLine

/-- Actual same-row image and J-dual normalization produces the remaining
eight harmonic classes itself, rather than receiving a desired branch. -/
theorem normalized_eight (f : Form) (A : End) (l r : FourLineCode) (h : PairedRanges f A l r) :
    ∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧
      normalizedMap f A l.val r.val = c • model f baseCode baseCode k :=
  paired_eight f _ baseCode baseCode (normalized_paired f A l r h)

def inverseStabilizer (f : Form) (k : Fin 8) : End :=
  sandwich (inverseKernel f (stabilizerPair k).1) (inverseKernel f (stabilizerPair k).2)

theorem inverseStabilizer_left (f : Form) (k : Fin 8) :
    inverseStabilizer f k * sandwich (kernel f (stabilizerPair k).1)
      (kernel f (stabilizerPair k).2) = 1 := by
  rw [inverseStabilizer,sandwich_comp,inverseKernel_left,inverseKernel_right,sandwich_one]

theorem inverseStabilizer_chart (f : Form) (k : Fin 8) :
    inverseStabilizer f k * (lineMatrix f baseLine * parameter k) =
      (embed (stabilizerSign k : Scalar))⁻¹ • lineMatrix f baseLine := by
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 2) ℂ => inverseStabilizer f k * M)
    (stabilizer_chart f k)
  rw [←Matrix.mul_assoc,inverseStabilizer_left,Matrix.one_mul,Matrix.mul_smul] at hh
  calc
    inverseStabilizer f k * (lineMatrix f baseLine * parameter k) =
        (embed (stabilizerSign k : Scalar))⁻¹ •
          (embed (stabilizerSign k : Scalar) •
            (inverseStabilizer f k * (lineMatrix f baseLine * parameter k))) := by
      rw [smul_smul,inv_mul_cancel₀ (stabilizer_scalar_ne k),one_smul]
    _ = (embed (stabilizerSign k : Scalar))⁻¹ • lineMatrix f baseLine :=
      congrArg (fun M => (embed (stabilizerSign k : Scalar))⁻¹ • M) hh.symm

theorem parameter_zero : parameter 0 = (1 : SmallMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [parameter,parameterZ,Matrix.one_apply]

/-- The produced class is eliminated by its ACTUAL old kernel stabilizer.
The new comparison scalar is an output, not a normalization premise. -/
theorem normalize_class (f : Form) (A : End) (l r : FourLineCode) (h : PairedRanges f A l r) :
    ∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧
      inverseStabilizer f k * normalizedMap f A l.val r.val = c • model f baseCode baseCode 0 := by
  obtain ⟨k,d,hd,he⟩ := normalized_eight f A l r h
  let z := embed (stabilizerSign k : Scalar)
  have hz : z ≠ 0 := stabilizer_scalar_ne k
  refine ⟨k,d/z,div_ne_zero hd hz,?_⟩
  calc
    inverseStabilizer f k * normalizedMap f A l.val r.val =
        d • ((inverseStabilizer f k * (lineMatrix f baseLine*parameter k)) *
          (liftSmall (quotientMatrix f baseLine))⁻¹ * dualMatrix f baseLine) := by
      rw [he]
      simp only [model,baseCode,Matrix.mul_smul,Matrix.mul_assoc]
    _ = (d/z) • model f baseCode baseCode 0 := by
      rw [inverseStabilizer_chart,Matrix.smul_mul,Matrix.smul_mul,smul_smul]
      simp only [model,baseCode,parameter_zero,Matrix.mul_one,div_eq_mul_inv,z]

def xConjugateIndex (f : Form) (k : Fin 24) : Fin 24 :=
  movedIndex (flipIndex f) (flipIndex f) k

def xConjugateScale (f : Form) (k : Fin 24) : Scalar :=
  flipScale f * flipScale f * movedScale (flipIndex f) (flipIndex f) k

theorem nativeX_kernel (f : Form) :
    Holant.Certificates.MatchingContractionClosure.X = embed (flipScale f) • kernel f (flipIndex f) := by
  change Matrix.of Holant.Certificates.MatchingProductBridge.X = _
  rw [←complexMatrix_flip,flip_marked_certificate f,complexMatrix_ms]
  rfl

/-- Conjugation by the ACTUAL native X is an old root-table product. -/
theorem xConjugate_kernel (f : Form) (k : Fin 24) :
    Holant.Certificates.MatchingContractionClosure.X * kernel f k *
      Holant.Certificates.MatchingContractionClosure.X =
      embed (xConjugateScale f k) • kernel f (xConjugateIndex f k) := by
  rw [Matrix.mul_assoc]
  simp only [nativeX_kernel f,Matrix.mul_smul,Matrix.smul_mul,
    kernel_product,smul_smul]
  ext u v
  simp only [xConjugateScale,xConjugateIndex,movedIndex,movedScale,embed_mul,
    Matrix.smul_apply,smul_eq_mul]
  ring

theorem xConjugateScale_ne (f : Form) (k : Fin 24) : embed (xConjugateScale f k) ≠ 0 :=
  embed_ne_zero (mul_ne_zero (mul_ne_zero (flipScale_nonzero f) (flipScale_nonzero f))
    (movedScale_ne _ _ _))

def inverseCodes (f : Form) (l r : Fin 122) : Fin 4 → Fin 24 :=
  ![inverseIndex (orbitPair r).1,inverseIndex (orbitPair r).2,
    inverseIndex (orbitPair l).1,xConjugateIndex f (inverseIndex (orbitPair l).2)]

def inverseReverse : Fin 4 → Bool := ![false,true,false,true]

def inverseSlots (f : Form) (l r : Fin 122) : Fin 4 → BinaryMatrix :=
  ![inverseKernel f (orbitPair r).1,(inverseKernel f (orbitPair r).2).transpose,
    inverseKernel f (orbitPair l).1,
    (Holant.Certificates.MatchingContractionClosure.X * inverseKernel f (orbitPair l).2 *
      Holant.Certificates.MatchingContractionClosure.X).transpose]

def inverseSlotScale (f : Form) (l r : Fin 122) : Fin 4 → ℂ :=
  ![embed (inverseScale (orbitPair r).1),embed (inverseScale (orbitPair r).2),
    embed (inverseScale (orbitPair l).1),embed (inverseScale (orbitPair l).2)*
      embed (xConjugateScale f (inverseIndex (orbitPair l).2))]

theorem inverseSlotScale_ne (f : Form) (l r : Fin 122) (p : Fin 4) :
    inverseSlotScale f l r p ≠ 0 := by
  fin_cases p
  · exact inverseScale_ne _
  · exact inverseScale_ne _
  · exact inverseScale_ne _
  · exact mul_ne_zero (inverseScale_ne _) (xConjugateScale_ne _ _)

theorem inverseSlots_scale (f : Form) (l r : Fin 122) :
    inverseSlots f l r = fun p => inverseSlotScale f l r p •
      (if inverseReverse p then (kernel f (inverseCodes f l r p)).transpose
        else kernel f (inverseCodes f l r p)) := by
  funext p
  fin_cases p <;> simp only [inverseSlots,inverseSlotScale,inverseReverse,inverseCodes,
    inverseKernel,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Bool.false_eq_true,ite_false,ite_true,Matrix.mul_smul,
    Matrix.smul_mul,xConjugate_kernel,smul_smul,Matrix.transpose_smul]


/-- Inverse image action, with the right-X correction retained at the two
output ports; inverse J-dual action supplies both input transposes. -/
theorem inverse_tensor (f : Form) (q : FourTensor) (l r : Fin 122) :
    Signature.coordinateAction (inverseSlots f l r) q =
      reconstruct (rightX * normalizedMap f (transferMatrix q (Equiv.refl _)) l r) := by
  have ho : rightX * inverseOrbit f l * rightX =
      sandwich (inverseKernel f (orbitPair l).1)
        (Holant.Certificates.MatchingContractionClosure.X * inverseKernel f (orbitPair l).2 *
          Holant.Certificates.MatchingContractionClosure.X) := by
    rw [rightX,inverseOrbit,sandwich_comp,sandwich_comp]
    simp only [Matrix.one_mul,Matrix.mul_one,Matrix.mul_assoc]
  rw [inverseSlots,tensor_dressing,Matrix.transpose_transpose,
    ←sharp_sandwich,←ho]
  change reconstruct ((rightX*inverseOrbit f l*rightX)*cardMatrix q*
    sharp (inverseOrbit f r)) = _
  have ht : transferMatrix q (Equiv.refl _) = rightX*cardMatrix q := rfl
  rw [ht]
  simp only [normalizedMap,Matrix.mul_assoc]

def stabilizerInverseCodes (f : Form) (k : Fin 8) : Fin 4 → Fin 24 :=
  ![0,0,inverseIndex (stabilizerPair k).1,xConjugateIndex f (inverseIndex (stabilizerPair k).2)]

def stabilizerInverseReverse : Fin 4 → Bool := ![false,false,false,true]

def stabilizerInverseScale (f : Form) (k : Fin 8) : Fin 4 → ℂ :=
  ![1,1,embed (inverseScale (stabilizerPair k).1),embed (inverseScale (stabilizerPair k).2)*
    embed (xConjugateScale f (inverseIndex (stabilizerPair k).2))]

def stabilizerInverseSlots (f : Form) (k : Fin 8) : Fin 4 → BinaryMatrix :=
  ![1,1,inverseKernel f (stabilizerPair k).1,
    (Holant.Certificates.MatchingContractionClosure.X * inverseKernel f (stabilizerPair k).2 *
      Holant.Certificates.MatchingContractionClosure.X).transpose]

theorem stabilizerInverseScale_ne (f : Form) (k : Fin 8) (p : Fin 4) :
    stabilizerInverseScale f k p ≠ 0 := by
  fin_cases p
  · exact one_ne_zero
  · exact one_ne_zero
  · exact inverseScale_ne _
  · exact mul_ne_zero (inverseScale_ne _) (xConjugateScale_ne _ _)

theorem stabilizerInverseSlots_scale (f : Form) (k : Fin 8) :
    stabilizerInverseSlots f k = fun p => stabilizerInverseScale f k p •
      (if stabilizerInverseReverse p then (kernel f (stabilizerInverseCodes f k p)).transpose
        else kernel f (stabilizerInverseCodes f k p)) := by
  funext p
  fin_cases p <;> simp only [stabilizerInverseSlots,stabilizerInverseScale,
    stabilizerInverseReverse,stabilizerInverseCodes,inverseKernel,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Bool.false_eq_true,ite_false,ite_true,kernel_zero,one_smul,Matrix.mul_smul,
    Matrix.smul_mul,xConjugate_kernel,smul_smul,Matrix.transpose_smul]


theorem stabilizer_inverse_tensor (f : Form) (q : FourTensor) (k : Fin 8) :
    Signature.coordinateAction (stabilizerInverseSlots f k) q =
      reconstruct (rightX * inverseStabilizer f k * transferMatrix q (Equiv.refl _)) := by
  have ho : rightX * inverseStabilizer f k * rightX =
      sandwich (inverseKernel f (stabilizerPair k).1)
        (Holant.Certificates.MatchingContractionClosure.X * inverseKernel f (stabilizerPair k).2 *
          Holant.Certificates.MatchingContractionClosure.X) := by
    rw [rightX,inverseStabilizer,sandwich_comp,sandwich_comp]
    simp only [Matrix.one_mul,Matrix.mul_one,Matrix.mul_assoc]
  rw [stabilizerInverseSlots,tensor_dressing,Matrix.transpose_transpose,Matrix.transpose_one,
    sandwich_one,Matrix.mul_one,←ho]
  have ht : transferMatrix q (Equiv.refl _) = rightX*cardMatrix q := rfl
  rw [ht]
  simp only [Matrix.mul_assoc]

end

noncomputable section
private theorem basis_dual (i j : Fin 4) :
    (∑ a : Bool,∑ b : Bool,quaternionBasis j a b*
      Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual i a b) =
        if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [quaternionBasis,Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual,
      Q0,Q1,Q2,Q3,Signature.equality,Fintype.sum_bool] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem contract_reconstruct (A : End) (j : Fin 4) :
    rawCard (reconstruct A) (Equiv.refl _) (Matrix.of (quaternionBasis j)) =
      assemble (fun i => A i j) := by
  ext c d
  change (∑ a : Bool,∑ b : Bool,quaternionBasis j a b*
    (∑ i : Fin 4,Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual i a b*
      assemble (fun l => A l i) c d)) = _
  simp only [Finset.mul_sum,mul_assoc]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [←mul_assoc,←Finset.sum_mul,basis_dual]
  simp

/-- Both sides of actual quaternion tomography are proved. This inverse
is needed to compose the two ORIGINAL physical dressing stages. -/
theorem card_reconstruct (A : End) : cardMatrix (reconstruct A) = A := by
  ext i j
  change coordinates (rawCard (reconstruct A) (Equiv.refl _)
    (Matrix.of (quaternionBasis j))) i = A i j
  rw [contract_reconstruct]
  change quaternionCoefficient (assemble (fun l => A l j)) i = A i j
  rw [coefficient_assemble]

theorem transfer_reconstruct (A : End) :
    transferMatrix (reconstruct (rightX*A)) (Equiv.refl _) = A := by
  change rightX*cardMatrix (reconstruct (rightX*A)) = A
  rw [card_reconstruct,←Matrix.mul_assoc,rightX_square,Matrix.one_mul]

theorem card_smul (c : ℂ) (q : FourTensor) : cardMatrix (c • q) = c • cardMatrix q := by
  ext i j
  change coordinates (rawCard (c • q) (Equiv.refl _) (Matrix.of (quaternionBasis j))) i =
    (c • coordinates (rawCard q (Equiv.refl _) (Matrix.of (quaternionBasis j)))) i
  have h := congrArg (fun M : BinaryMatrix=>coordinates M)
    (GlobalCloseCompletionTetrahedralLiteralDeck.rawCard_scale_tensor q (Equiv.refl _)
      (Matrix.of (quaternionBasis j)) c)
  rw [map_smul] at h
  exact congrFun h i

theorem transfer_smul (c : ℂ) (q : FourTensor) :
    transferMatrix (c • q) (Equiv.refl _) = c • transferMatrix q (Equiv.refl _) := by
  change rightX*cardMatrix (c • q) = c • (rightX*cardMatrix q)
  rw [card_smul,Matrix.mul_smul]

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
