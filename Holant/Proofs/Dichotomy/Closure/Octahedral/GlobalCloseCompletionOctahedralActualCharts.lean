import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralChartsCertificates
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open scoped Matrix BigOperators

noncomputable section

private theorem point_agree (f : Form) (i : Fin 24) :
    RankThree.point f i=point f i := rfl

def liftPlane (v : RawPlane) : Plane := fun i => embed (v i)

def liftSmall (B : RawSmallMatrix) : SmallMatrix := fun i j => embed (B i j)

theorem lift_rawRoot (k : Fin 4) : liftPlane (rawRoot k) = root k := by
  ext a
  change embedding (rootZ k a : Scalar) = (rootZ k a : ℂ)
  simp

private theorem embed_rawRoot (k : Fin 4) (a : Fin 2) :
    embed (rawRoot k a)=root k a := congrFun (lift_rawRoot k) a

theorem lift_plane_smul (c : Scalar) (v : RawPlane) :
    liftPlane (c • v) = embed c • liftPlane v := by
  ext i
  exact embed_mul _ _

theorem lift_plane_mulVec (B : RawSmallMatrix) (v : RawPlane) :
    liftPlane (B *ᵥ v) = liftSmall B *ᵥ liftPlane v := by
  ext i
  simp [liftPlane,liftSmall,Matrix.mulVec,dotProduct,Fin.sum_univ_two,embed_add,embed_mul]

def lineMatrix (f : Form) (t : Fin 122) : Matrix (Fin 4) (Fin 2) ℂ :=
  fun i a => point f (canonicalPair t a) i

def leftMatrix (f : Form) (t : Fin 122) : Matrix (Fin 2) (Fin 4) ℂ :=
  fun a i => point f (canonicalPair t a) i/embed (lineNorm t)

def dualMatrix (f : Form) (t : Fin 122) : Matrix (Fin 2) (Fin 4) ℂ :=
  fun a i => frobeniusSigns i*point f (canonicalPair t a) i

def dualSection (f : Form) (t : Fin 122) : Matrix (Fin 4) (Fin 2) ℂ :=
  fun i a => frobeniusSigns i*point f (canonicalPair t a) i/embed (lineNorm t)

theorem embed_rawDot (u v : RankThree.RawVector) :
    embed (RankThree.rawDot u v) = ∑ i : Fin 4,RankThree.lift u i*RankThree.lift v i := by
  simp [RankThree.rawDot,RankThree.lift,Fin.sum_univ_succ,embed_add,embed_mul,add_assoc]

theorem line_gram (f : Form) (t : FourLineCode) (a b : Fin 2) :
    (∑ i : Fin 4,point f (canonicalPair t.val a) i*point f (canonicalPair t.val b) i) =
      if a = b then embed (lineNorm t.val) else 0 := by
  have h := (finite_line_data t.val t.property).2.1 f a b
  have hh := congrArg embed h
  rw [embed_rawDot] at hh
  by_cases hab : a = b <;> simpa [hab,embed_zero,RankThree.lift_point,point_agree] using hh

theorem left_inverse (f : Form) (t : FourLineCode) :
    leftMatrix f t.val*lineMatrix f t.val = 1 := by
  ext a b
  simp only [Matrix.mul_apply,leftMatrix,lineMatrix,div_mul_eq_mul_div,←Finset.sum_div,
    line_gram f t a b,Matrix.one_apply]
  split_ifs <;> simp [embed_ne_zero (finite_line_data t.val t.property).1]

theorem dual_section (f : Form) (t : FourLineCode) :
    dualMatrix f t.val*dualSection f t.val = 1 := by
  ext a b
  have ht (i : Fin 4) : (frobeniusSigns i*point f (canonicalPair t.val a) i)*
      (frobeniusSigns i*point f (canonicalPair t.val b) i/embed (lineNorm t.val)) =
      (point f (canonicalPair t.val a) i*point f (canonicalPair t.val b) i)/embed (lineNorm t.val) := by
    calc
      _ = (frobeniusSigns i*frobeniusSigns i)*
          (point f (canonicalPair t.val a) i*point f (canonicalPair t.val b) i)/
            embed (lineNorm t.val) := by ring
      _ = _ := by rw [signs_square,one_mul]
  simp only [Matrix.mul_apply,dualMatrix,dualSection,ht,←Finset.sum_div,
    line_gram f t a b,Matrix.one_apply]
  split_ifs <;> simp [embed_ne_zero (finite_line_data t.val t.property).1]

theorem line_root (f : Form) (t : FourLineCode) (k : Fin 4) :
    point f (lineKey t.val k) = embed (lineScale t.val k) •
      (lineMatrix f t.val *ᵥ root k) := by
  have hd := finite_line_data t.val t.property
  have hk := hd.2.2.2.1 k
  have hh := hd.2.2.1 f (lineKey t.val k) hk.1
  rw [hk.2.2] at hh
  have he := congrArg RankThree.lift hh
  simp only [RankThree.lift_add,RankThree.lift_smul,RankThree.lift_point,point_agree] at he
  ext i
  have hi := congrFun he i
  simpa [lineMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    embed_mul,embed_rawRoot,Pi.smul_apply,smul_eq_mul,mul_add,
      mul_assoc,mul_left_comm,mul_comm] using hi

theorem line_scale_ne (t : FourLineCode) (k : Fin 4) : embed (lineScale t.val k) ≠ 0 :=
  embed_ne_zero ((finite_line_data t.val t.property).2.2.2.1 k).2.1

theorem line_chart_root (f : Form) (t : FourLineCode) (k : Fin 4) :
    leftMatrix f t.val *ᵥ point f (lineKey t.val k) =
      embed (lineScale t.val k) • root k := by
  rw [line_root,Matrix.mulVec_smul,Matrix.mulVec_mulVec,left_inverse,Matrix.one_mulVec]

theorem line_harmonic (f : Form) (t : FourLineCode) :
    harmonic (fun k => leftMatrix f t.val *ᵥ point f (lineKey t.val k)) = 0 := by
  simp only [line_chart_root]
  exact harmonic_scaled_roots _

theorem line_separate (f : Form) (t : FourLineCode) {i j : Fin 4} (hij : i ≠ j) :
    cross (leftMatrix f t.val *ᵥ point f (lineKey t.val i))
      (leftMatrix f t.val *ᵥ point f (lineKey t.val j)) ≠ 0 := by
  simp only [line_chart_root]
  exact scaled_roots_separate _ (line_scale_ne t) hij

theorem line_cover (t : FourLineCode) {r : Fin 24} (hr : r ∈ globalLine .octahedral t.val) :
    ∃ k : Fin 4,r = lineKey t.val k := (finite_line_data t.val t.property).2.2.2.2 r hr

theorem dual_point (f : Form) (t : Fin 122) (r : Fin 24) :
    dualMatrix f t *ᵥ point f r = liftPlane (projected f t r) := by
  ext a
  fin_cases a
  · change pairing (point f (canonicalPair t 0)) (point f r) =
      embed (rawPair (rawPoint f (canonicalPair t 0)) (rawPoint f r))
    simpa only [RankThree.lift_point,point_agree] using
      (RankThree.embed_pair (rawPoint f (canonicalPair t 0)) (rawPoint f r)).symm
  · change pairing (point f (canonicalPair t 1)) (point f r) =
      embed (rawPair (rawPoint f (canonicalPair t 1)) (rawPoint f r))
    simpa only [RankThree.lift_point,point_agree] using
      (RankThree.embed_pair (rawPoint f (canonicalPair t 1)) (rawPoint f r)).symm

theorem quotient_det_ne (f : Form) (t : FourLineCode) :
    det2 (liftSmall (quotientMatrix f t.val)) ≠ 0 := by
  have hn := embed_ne_zero (finite_quotient_data f t.val t.property).1
  simpa [det2,rawDet,liftSmall,embed_sub,embed_mul] using hn

theorem quotient_root (f : Form) (t : FourLineCode) (k : Fin 4) :
    liftSmall (quotientMatrix f t.val) *ᵥ root k =
      (embed (quotientScale f t.val k))⁻¹ •
        (dualMatrix f t.val *ᵥ point f (quotientKey f t.val k)) := by
  have hh := congrArg liftPlane ((finite_quotient_data f t.val t.property).2.1 k).2.2
  simpa only [lift_plane_mulVec,lift_rawRoot,lift_plane_smul,embed_inv,dual_point] using hh

theorem quotient_scale_ne (f : Form) (t : FourLineCode) (k : Fin 4) :
    embed (quotientScale f t.val k) ≠ 0 :=
  embed_ne_zero ((finite_quotient_data f t.val t.property).2.1 k).2.1

theorem quotient_chart_root (f : Form) (t : FourLineCode) (k : Fin 4) :
    (liftSmall (quotientMatrix f t.val))⁻¹ *ᵥ
      (dualMatrix f t.val *ᵥ point f (quotientKey f t.val k)) =
      embed (quotientScale f t.val k) • root k := by
  let B := liftSmall (quotientMatrix f t.val)
  let s := embed (quotientScale f t.val k)
  have hs : s ≠ 0 := quotient_scale_ne f t k
  have he : dualMatrix f t.val *ᵥ point f (quotientKey f t.val k) = s • (B *ᵥ root k) := by
    rw [quotient_root,smul_smul,mul_inv_cancel₀ hs,one_smul]
  have hd : B.det ≠ 0 := by simpa only [B,det2,Matrix.det_fin_two] using quotient_det_ne f t
  rw [he,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]

theorem quotient_harmonic (f : Form) (t : FourLineCode) :
    harmonic (fun k => (liftSmall (quotientMatrix f t.val))⁻¹ *ᵥ
      (dualMatrix f t.val *ᵥ point f (quotientKey f t.val k))) = 0 := by
  simp only [quotient_chart_root]
  exact harmonic_scaled_roots _

theorem quotient_separate (f : Form) (t : FourLineCode) {i j : Fin 4} (hij : i ≠ j) :
    cross ((liftSmall (quotientMatrix f t.val))⁻¹ *ᵥ
      (dualMatrix f t.val *ᵥ point f (quotientKey f t.val i)))
      ((liftSmall (quotientMatrix f t.val))⁻¹ *ᵥ
      (dualMatrix f t.val *ᵥ point f (quotientKey f t.val j))) ≠ 0 := by
  simp only [quotient_chart_root]
  exact scaled_roots_separate _ (quotient_scale_ne f t) hij

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
