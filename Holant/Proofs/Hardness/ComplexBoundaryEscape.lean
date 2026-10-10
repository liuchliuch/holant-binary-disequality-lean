import Holant.Proofs.Hardness.ThreeModeTriangleObstruction
import Holant.Proofs.Hardness.GeneralGeometricCapLocal
import Holant.Proofs.Hardness.LabelledNetwork

/-! A physical two-copy escape for the complex selfdual boundary c=a+b.
When c and b-a have equal modulus, nonzero a,b are perpendicular in the
complex plane. Two original rows and two native-X edges produce another
boundary triple with strictly unequal spectral moduli. This is an access
lemma, not a supplied spectral promise or a local directed pin. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexBoundaryEscape
open Holant Holant.Complexity FixedGadgetSubstitution
namespace S
export ThreeModeSignatures (original)
end S
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R

variable {K : Type} [Field K]
def first (a b : K) := 2*a*(a+b)
def second (_a b : K) := b^2
def third (a b : K) := a^2+(a+b)^2

theorem boundary (a b : K) : third a b=first a b+second a b := by
  unfold first second third
  ring

def one (a b : K) : Network K 4 :=
  R.reindex (Network.corolla (S.original a b (a+b))) SignedTwoCoefficientSignatures.middleSwap

def network (a b : K) : Network K 4 :=
  R.reindex (ExactTwoChain.series (one a b) (one a b)) SignedTwoCoefficientSignatures.middleSwap

theorem denote (a b : K) :
    (network a b).denote=S.original (first a b) (second a b) (third a b) := by
  have ho : (one a b).denote=S.original a (a+b) b := by
    rw [one,R.reindex_denote,Network.denote_corolla,ThreeModeTriangleObstruction.swap_bc]
  rw [network,R.reindex_denote,
    ThreeModeTriangleObstruction.series_original _ _ _ _ _ _ _ _ ho ho,
    ThreeModeTriangleObstruction.swap_bc]
  unfold first second third
  congr 1 <;> ring

def labels (a b : K) : Labelling (network a b).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by fin_cases v <;> rfl
  edge _ := 0
abbrev template (a b : K) := (labels a b).template

theorem valid (a b : K) : (template a b).WellFormed 1 1 (fun _=>4) := (labels a b).wellFormed

theorem counts (a b : K) :
    (template a b).vertices.length=2 ∧ (template a b).edges.length=2 := ⟨rfl,rfl⟩

theorem records (a b : K) :
    (template a b).boundary=4 ∧ (template a b).vertices=
      [(0,[.inl 0,.inr (1,false),.inr (0,false),.inl 3]),
       (0,[.inr (1,true),.inl 1,.inl 2,.inr (0,true)])] ∧
      (template a b).edges=[0,0] := ⟨rfl,rfl,rfl⟩

theorem template_denote (a b : K) :
    ((template a b).network (valid a b) (fun _ : Fin 1=>S.original a b (a+b))
      (fun _ : Fin 1=>Signature.disequality)).denote=
      S.original (first a b) (second a b) (third a b) := by
  rw [←denote]
  apply Labelling.denote_template_of_labels (labels a b) _ _ (network a b).vertex (network a b).edge
  · intro v x; fin_cases v <;> rfl
  · intro e x y; fin_cases e <;> rfl

def inner (a b : ℂ) : ℝ := a.re*b.re+a.im*b.im

theorem balanced_inner (a b : ℂ) (h : ‖a+b‖=‖b-a‖) : inner a b=0 := by
  have hs := congrArg (fun r : ℝ=>r^2) h
  rw [Complex.sq_norm,Complex.sq_norm] at hs
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im] at hs
  unfold inner
  nlinarith

theorem third_normSq_formula (a b : ℂ) :
    Complex.normSq (third a b)=4*(Complex.normSq a)^2+(Complex.normSq b)^2+
      4*inner a b*(2*Complex.normSq a+Complex.normSq b+2*inner a b) := by
  simp only [third,inner,Complex.normSq_apply,pow_two,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im]
  ring

theorem difference_normSq_formula (a b : ℂ) :
    Complex.normSq (second a b-first a b)=4*(Complex.normSq a)^2+(Complex.normSq b)^2+
      8*Complex.normSq a*Complex.normSq b+
      4*inner a b*(2*Complex.normSq a-Complex.normSq b-2*inner a b) := by
  simp only [first,second,inner,Complex.normSq_apply,pow_two,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem third_nonzero (a b : ℂ) (ha : a≠0) (h : ‖a+b‖=‖b-a‖) : third a b≠0 := by
  intro hz
  have hf := third_normSq_formula a b
  rw [balanced_inner a b h,hz] at hf
  have hp := Complex.normSq_pos.mpr ha
  norm_num at hf
  nlinarith [sq_nonneg (Complex.normSq b)]

theorem strict_moduli (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (h : ‖a+b‖=‖b-a‖) : ‖third a b‖<‖second a b-first a b‖ := by
  have hzero := balanced_inner a b h
  have h1 := third_normSq_formula a b
  have h2 := difference_normSq_formula a b
  rw [hzero] at h1 h2
  have hp := mul_pos (Complex.normSq_pos.mpr ha) (Complex.normSq_pos.mpr hb)
  have hs : ‖third a b‖^2<‖second a b-first a b‖^2 := by
    rw [Complex.sq_norm,Complex.sq_norm]
    nlinarith
  nlinarith [norm_nonneg (third a b),norm_nonneg (second a b-first a b)]

theorem difference_nonzero (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (h : ‖a+b‖=‖b-a‖) : second a b-first a b≠0 := by
  intro hz
  have he := strict_moduli a b ha hb h
  rw [hz,norm_zero] at he
  exact (not_lt_of_ge (norm_nonneg _)) he

theorem ratio_infinite (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (h : ‖a+b‖=‖b-a‖) (n : ℕ) (hn : 0<n) :
    (third a b/(second a b-first a b))^n≠1 :=
  GeneralGeometricCapLocal.infinite_of_unequal_norms _ _ (difference_nonzero a b ha hb h)
    (ne_of_lt (strict_moduli a b ha hb h)) n hn

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexBoundaryEscape
