import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralActualCharts
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Coefficient extraction from the preserved marked-octahedral proof. The small matrix is computed from the SAME original
A and its actual paired ranges. Kernel identification uses the actual J
adjoint. A small map, a survivor or a normal form is never a caller input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open scoped Matrix BigOperators

theorem pairing_add_left (u v w : V) : pairing (u+v) w = pairing u w+pairing v w := by
  simp [pairing,add_mul,mul_add,Finset.sum_add_distrib]

theorem lineMatrix_expansion (f : Form) (t : Fin 122) (v : Plane) :
    lineMatrix f t *ᵥ v = ∑ a : Fin 2,v a • point f (canonicalPair t a) := by
  ext i
  simp [lineMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,mul_comm]

theorem dual_value (f : Form) (t : Fin 122) (v : V) (a : Fin 2) :
    (dualMatrix f t *ᵥ v) a = pairing (point f (canonicalPair t a)) v := rfl

/-- Both directions retain the SAME bilinear kernel of A. In particular
the quotient cannot be replaced by a freely chosen root-polynomial zero. -/
theorem kernel_iff (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) (v : V) :
    A *ᵥ v = 0 ↔ dualMatrix f r.val *ᵥ v = 0 := by
  constructor
  · intro hv
    ext a
    rw [dual_value]
    simpa using (pairing_range_scale (c := (0 : ℂ)) (s := (0 : V))
      (h.rightPair a) (by simpa using hv))
  · intro hv
    have hp (a : Fin 2) : pairing (point f (canonicalPair r.val a)) v = 0 := by
      simpa only [dual_value,Pi.zero_apply] using congrFun hv a
    have hz (u : V) (hu : u ∈ rootPlane f (canonicalPair r.val)) : pairing u v = 0 := by
      obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
      rw [Fin.sum_univ_two] at hc
      rw [←hc,pairing_add_left,pairing_smul_left,pairing_smul_left,hp 0,hp 1]
      simp
    by_contra hn
    obtain ⟨w,hw⟩ := pairing_nonzero hn
    apply hw
    rw [pairing_adjoint,pairing_symm v]
    apply hz
    rw [h.rightSpan]
    exact ⟨w,rfl⟩

theorem range_recovery (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) {v : V} (hv : v ∈ LinearMap.range A.mulVecLin) :
    lineMatrix f l.val *ᵥ (leftMatrix f l.val *ᵥ v) = v := by
  have hm : v ∈ rootPlane f (canonicalPair l.val) := by rwa [h.leftSpan]
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
  rw [←lineMatrix_expansion] at hc
  rw [←hc,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    Matrix.mul_assoc,left_inverse,Matrix.mul_one]

theorem section_same_image (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) (v : V) :
    A *ᵥ (dualSection f r.val *ᵥ (dualMatrix f r.val *ᵥ v)) = A *ᵥ v := by
  have hz : dualMatrix f r.val *ᵥ
      (dualSection f r.val *ᵥ (dualMatrix f r.val *ᵥ v)-v) = 0 := by
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,dual_section,Matrix.one_mulVec,sub_self]
  have hh := (kernel_iff f A l r h _).mpr hz
  rw [Matrix.mulVec_sub] at hh
  exact sub_eq_zero.mp hh

def induced (f : Form) (A : End) (l r : FourLineCode) : SmallMatrix :=
  leftMatrix f l.val*A*dualSection f r.val*liftSmall (quotientMatrix f r.val)

theorem base_reconstruction (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) :
    A = lineMatrix f l.val*(leftMatrix f l.val*A*dualSection f r.val)*dualMatrix f r.val := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simp only [←Matrix.mulVec_mulVec]
  rw [section_same_image f A l r h]
  exact (range_recovery f A l r h ⟨v,rfl⟩).symm

theorem induced_zero (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) {v : Plane} (hv : induced f A l r *ᵥ v = 0) : v = 0 := by
  let B := liftSmall (quotientMatrix f r.val)
  let z := dualSection f r.val *ᵥ (B *ᵥ v)
  have hl : leftMatrix f l.val *ᵥ (A *ᵥ z) = 0 := by
    simpa only [induced,B,z,←Matrix.mulVec_mulVec] using hv
  have ha : A *ᵥ z = 0 := by
    calc
      A *ᵥ z = lineMatrix f l.val *ᵥ (leftMatrix f l.val *ᵥ (A *ᵥ z)) :=
        (range_recovery f A l r h (v := A *ᵥ z) ⟨z,rfl⟩).symm
      _ = 0 := by rw [hl,Matrix.mulVec_zero]
  have hq := (kernel_iff f A l r h z).mp ha
  have hb : B *ᵥ v = 0 := by
    simpa only [z,Matrix.mulVec_mulVec,←Matrix.mul_assoc,dual_section,Matrix.one_mul] using hq
  apply Matrix.eq_zero_of_mulVec_eq_zero (M := B) _ hb
  simpa only [B,det2,Matrix.det_fin_two] using quotient_det_ne f r

theorem induced_det_ne (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) : det2 (induced f A l r) ≠ 0 := by
  intro hd
  have hd' : (induced f A l r).det = 0 := by simpa only [det2,Matrix.det_fin_two] using hd
  obtain ⟨v,hv,hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd'
  exact hv (induced_zero f A l r h hz)

theorem quotient_same_image (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) (k : Fin 4) :
    A *ᵥ (dualSection f r.val *ᵥ
      (liftSmall (quotientMatrix f r.val) *ᵥ root k)) =
    (embed (quotientScale f r.val k))⁻¹ • (A *ᵥ point f (quotientKey f r.val k)) := by
  rw [quotient_root,Matrix.mulVec_smul,Matrix.mulVec_smul,
    section_same_image f A l r h]

theorem root_ne_zero (k : Fin 4) : root k ≠ 0 := by
  fin_cases k
  · intro h
    have hh := congrFun h 0
    norm_num [root,rootZ] at hh
  · intro h
    have hh := congrFun h 1
    norm_num [root,rootZ] at hh
  · intro h
    have hh := congrFun h 0
    norm_num [root,rootZ] at hh
  · intro h
    have hh := congrFun h 0
    norm_num [root,rootZ] at hh

/-- The SAME induced matrix sends all four internally produced quotient
directions to the SAME actual range's harmonic four root directions. -/
theorem induced_keeps (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) : Keeps (induced f A l r) := by
  intro k
  have hc : induced f A l r *ᵥ root k ≠ 0 := by
    intro hz
    exact root_ne_zero k (induced_zero f A l r h hz)
  have he : induced f A l r *ᵥ root k = (embed (quotientScale f r.val k))⁻¹ •
      (leftMatrix f l.val *ᵥ (A *ᵥ point f (quotientKey f r.val k))) := by
    simp only [induced,←Matrix.mulVec_mulVec]
    rw [quotient_same_image f A l r h,Matrix.mulVec_smul]
  have hn : A *ᵥ point f (quotientKey f r.val k) ≠ 0 := by
    intro hz
    apply hc
    rw [he,hz,Matrix.mulVec_zero,smul_zero]
  have hA := (twoSided_iff_equations f A).mpr h.polynomials
  obtain ⟨j,c,hc',hj⟩ := (roots_iff f _).mp
    ((hA.1 _ (point_mem f _)).resolve_left hn)
  have hm : point f j ∈ LinearMap.range A.mulVecLin := by
    refine ⟨c⁻¹ • point f (quotientKey f r.val k),?_⟩
    change A *ᵥ (c⁻¹ • point f (quotientKey f r.val k)) = point f j
    rw [Matrix.mulVec_smul,hj,smul_smul,inv_mul_cancel₀ hc',one_smul]
  have hj' : j ∈ globalLine .octahedral l.val := by
    rw [←h.left]
    exact (mem_rootIndices f _ j).mpr hm
  obtain ⟨m,rfl⟩ := line_cover l hj'
  refine ⟨m,(embed (quotientScale f r.val k))⁻¹*c*embed (lineScale l.val m),
    mul_ne_zero (mul_ne_zero (inv_ne_zero (quotient_scale_ne f r k)) hc') (line_scale_ne l m),?_⟩
  rw [he,hj,line_root,Matrix.mulVec_smul,Matrix.mulVec_smul,
    Matrix.mulVec_mulVec,left_inverse,Matrix.one_mulVec,smul_smul,smul_smul] <;>
    simp only [mul_assoc]

/-- Literal reconstruction of A from its two original secant indices and
an eight-valued parameter. This is a proof-coordinate expression, not a
replacement tensor alphabet or physical dressing. -/
def model (f : Form) (l r : FourLineCode) (k : Fin 8) : End :=
  lineMatrix f l.val*parameter k*(liftSmall (quotientMatrix f r.val))⁻¹*dualMatrix f r.val

theorem induced_smul (f : Form) (A : End) (l r : FourLineCode) (c : ℂ) :
    induced f (c • A) l r = c • induced f A l r := by
  simp only [induced,Matrix.mul_smul,Matrix.smul_mul]

theorem induced_model (f : Form) (l r : FourLineCode) (k : Fin 8) :
    induced f (model f l r k) l r = parameter k := by
  have hd : (liftSmall (quotientMatrix f r.val)).det ≠ 0 := by
    simpa only [det2,Matrix.det_fin_two] using quotient_det_ne f r
  simp only [induced,model,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (leftMatrix f l.val),left_inverse,Matrix.one_mul,
    ←Matrix.mul_assoc (dualMatrix f r.val),dual_section,Matrix.one_mul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.mul_one]

theorem model_class_unique (f : Form) (l r : FourLineCode) {k m : Fin 8} {c d : ℂ}
    (hc : c ≠ 0) (he : c • model f l r k = d • model f l r m) : k = m := by
  have hh := congrArg (fun A => induced f A l r) he
  simp only [induced_smul,induced_model] at hh
  exact parameter_class_unique hc hh

theorem induced_reconstruction (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) :
    A = lineMatrix f l.val*induced f A l r*
      (liftSmall (quotientMatrix f r.val))⁻¹*dualMatrix f r.val := by
  have hd : (liftSmall (quotientMatrix f r.val)).det ≠ 0 := by
    simpa only [det2,Matrix.det_fin_two] using quotient_det_ne f r
  rw [induced,Matrix.mul_assoc (lineMatrix f l.val)]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (liftSmall (quotientMatrix f r.val)),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using base_reconstruction f A l r h

theorem paired_eight (f : Form) (A : End) (l r : FourLineCode)
    (h : PairedRanges f A l r) :
    ∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧ A = c • model f l r k := by
  obtain ⟨k,c,hc,he⟩ := keeps_complete (induced f A l r)
    (induced_det_ne f A l r h) (induced_keeps f A l r h)
  refine ⟨k,c,hc,?_⟩
  rw [induced_reconstruction f A l r h,he,model]
  simp only [Matrix.mul_smul,Matrix.smul_mul]

theorem rank_two_eight_cells (f : Form) (A : End)
    (h : TwoSided (Roots f) A) (hr : A.rank = 2) :
    ∃ i j : Fin 18,∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧
      PairedRanges f A (fourEnumeration i) (fourEnumeration j) ∧
      A = c • model f (fourEnumeration i) (fourEnumeration j) k := by
  obtain ⟨i,j,hp⟩ := (rank_two_iff_18cells f A).mp ⟨h,hr⟩
  obtain ⟨k,c,hc,he⟩ := paired_eight f A _ _ hp
  exact ⟨i,j,k,c,hc,hp,he⟩

/-- The two sides' original polynomial tests and rank are retained even
after reconstruction. No claim that every one of 2592 parameters survives. -/
theorem rank_two_iff_eight_cells (f : Form) (A : End) :
    TwoSided (Roots f) A ∧ A.rank = 2 ↔
    ∃ i j : Fin 18,∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧
      PairedRanges f A (fourEnumeration i) (fourEnumeration j) ∧
      A = c • model f (fourEnumeration i) (fourEnumeration j) k := by
  refine ⟨fun h => rank_two_eight_cells f A h.1 h.2,?_⟩
  rintro ⟨i,j,k,c,hc,hp,he⟩
  exact ⟨(twoSided_iff_equations f A).mpr hp.polynomials,hp.rank⟩

/-- Move the ORIGINAL two-sided tests to the internally returned model.
The nonzero comparison scalar is cancelled, not discarded. -/
theorem selected_model_conditions (f : Form) (A : End) (l r : FourLineCode)
    (k : Fin 8) (c : ℂ) (hc : c ≠ 0) (h : PairedRanges f A l r)
    (he : A = c • model f l r k) :
    Equations f (model f l r k) ∧ (model f l r k).rank = 2 := by
  have hA := (twoSided_iff_equations f A).mpr h.polynomials
  have hM := twoSided_smul (roots_saturated f) hA c⁻¹
  have hh : TwoSided (Roots f) (model f l r k) := by
    simpa only [he,smul_smul,inv_mul_cancel₀ hc,one_smul] using hM
  refine ⟨(twoSided_iff_equations f _).mp hh,?_⟩
  have hr := Matrix.rank_smul_of_mem_nonZeroDivisors (model f l r k)
    (mem_nonZeroDivisors_of_ne_zero hc)
  rw [←hr,←he]
  exact h.rank

/-- A finite checked catalogue equivalence. Its tests are the EXISTING
literal two-sided polynomial system on these computed matrices, not a
free checker/completeness premise or a claim that all 2592 pass. -/
theorem rank_two_iff_checked_eight (f : Form) (A : End) :
    TwoSided (Roots f) A ∧ A.rank = 2 ↔
    ∃ i j : Fin 18,∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧
      A = c • model f (fourEnumeration i) (fourEnumeration j) k ∧
      Equations f (model f (fourEnumeration i) (fourEnumeration j) k) ∧
      (model f (fourEnumeration i) (fourEnumeration j) k).rank = 2 := by
  constructor
  · rintro ⟨h,hr⟩
    obtain ⟨i,j,k,c,hc,hp,he⟩ := rank_two_eight_cells f A h hr
    exact ⟨i,j,k,c,hc,he,selected_model_conditions f A _ _ k c hc hp he⟩
  · rintro ⟨i,j,k,c,hc,rfl,hm,hr⟩
    refine ⟨twoSided_smul (roots_saturated f) ((twoSided_iff_equations f _).mpr hm) c,?_⟩
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)]
    exact hr

theorem reconstruct_smul (c : ℂ) (A : End) : reconstruct (c • A) = c • reconstruct A := by
  have hs (i : Fin 4) : assemble (fun j => (c • A) j i) = c • assemble (fun j => A j i) := by
    exact map_smul coordinates.symm c (fun j => A j i)
  funext x
  simp only [reconstruct,hs,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change _ * (c * _) = _
  ring

/-- Undo only the actual right-X transfer, then use the old literal
quaternion reconstruction. The ORIGINAL ordered q4 tensor is recovered;
the proof chart has not become a port action or a physical dressing. -/
theorem same_q4 (f : Form) (q : FourTensor) (e : PortOrder) (l r : FourLineCode)
    (k : Fin 8) (c : ℂ) (he : transferMatrix q e = c • model f l r k) :
    relabel e q = c • reconstruct (rightX*model f l r k) := by
  have hd : cardMatrix (relabel e q) = rightX*transferMatrix q e := by
    rw [transferMatrix,←Matrix.mul_assoc,rightX_square,Matrix.one_mul]
  have hh := reconstruct_cardMatrix (relabel e q)
  rw [hd,he,Matrix.mul_smul,reconstruct_smul] at hh
  exact hh.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
