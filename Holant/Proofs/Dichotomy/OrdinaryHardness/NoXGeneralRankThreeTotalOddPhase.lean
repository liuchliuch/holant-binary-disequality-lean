import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalMasks
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalSignedMultiplicityPhase
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankThreeAlphaCore
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreePorts

/-! A total-odd triple character is incompatible with two parallel L pin
faces when the original square is Affine. Their squared mixed ratios must
coincide by the original square and oppose by the supported local phases. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankThreeTotalOddPhase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXLocalSignedMultiplicityPhase (original unitPhase unitPhase_nonzero)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
export OrdinaryNegativeSparseRankThreePorts (port word_code)
end P
namespace C
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
export OrdinaryNegativeRankThreeAlphaCore (eval_value value)
end C
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification (affine_signed_cross)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false

theorem cons_vector (bit : Bool) (x : Word 2) : Fin.cons bit x=![bit,x 0,x 1]:=by
  funext i
  fin_cases i <;> rfl

def cross (f : Signature AlgebraicComplex 2) : AlgebraicComplex:=
  f ![false,false]*f ![true,true]/(f ![false,true]*f ![true,false])
def slice (f : Signature AlgebraicComplex 3) (b : Bool) : Signature AlgebraicComplex 2:=
  fun x=>f (Fin.cons b x)

theorem cross_mul (f g : Signature AlgebraicComplex 2) :
    cross (fun x=>f x*g x)=cross f*cross g:=by
  simp only [cross,div_eq_mul_inv,mul_inv_rev]
  ring

theorem cross_prod {k : ℕ} (fs : Fin k→Signature AlgebraicComplex 2) :
    cross (fun x=>∏i,fs i x)=∏i,cross (fs i):=by
  simp only [cross,Finset.prod_div_distrib,Finset.prod_mul_distrib]

theorem cross_affine (f : Signature AlgebraicComplex 2) (full : ∀x,f x≠0) (good : Affine f) :
    cross f^2=1:=by
  have h:=B.affine_signed_cross f full good
  have eqn : (f ![false,false]*f ![true,true])^2=(f ![false,true]*f ![true,false])^2:=by
    rcases h with h|h
    · rw [h]
    · rw [h,neg_sq]
  rw [cross,div_pow,eqn,div_self (pow_ne_zero 2 (mul_ne_zero (full _) (full _)))]

theorem parallel (f : Signature AlgebraicComplex 3) (full : ∀x,f x≠0)
    (square : Affine (fun x=>f x^2)) : cross (slice f false)^2=cross (slice f true)^2:=by
  have h:=secondRatio_constant (fun x=>pow_ne_zero 2 (full x))
    (thirdTrivial_of_affine (fun x=>pow_ne_zero 2 (full x)) square)
    (basis 0) (basis 1) (basis 2)
  simp only [secondRatio,C.eval_value f] at h
  simp only [C.value,AffinePhase.xor,basis,origin] at h
  simpa [cross,slice,cons_vector,div_pow,mul_pow,mul_comm] using h.symm

def atom (q : Port 7) (b : Bool) : Signature AlgebraicComplex 2:=
  match q with
  | .inl bit=>fun _=>P.unitPhase bit
  | .inr (j,s)=>fun x=>P.unitPhase
      ((s ^^ C.codeSeven (Fin.cons b (origin 2)) j)&&(s ^^ C.codeSeven (Fin.cons b x) j))

theorem atom_cross (q : Port 7) :
    cross (atom q false)^2=(match q with | .inl _=>1 | .inr (j,_)=>if j=6 then -1 else 1)*
      cross (atom q true)^2:=by
  cases q with
  | inl bit=>cases bit <;> simp [atom,cross,P.unitPhase,zetaEight_ne_zero]
  | inr pair=>
      rcases pair with ⟨j,s⟩
      fin_cases j <;> cases s <;>
        norm_num [atom,cross,P.unitPhase,C.codeSeven,origin,cons_vector,←pow_two,
          zetaEight_ne_zero,zetaEight_pow_four,Holant.Marked.imaginaryUnit_ne_zero,imaginaryUnit_sq]

def phase {n : ℕ} (ps : Fin n→Port 7) (b : Bool) : Signature AlgebraicComplex 2:=
  fun x=>∏i,atom (ps i) b x

theorem phase_original {n : ℕ} (ps : Fin n→Port 7) (b : Bool) (x : Word 2) :
    phase ps b x=P.original ps (C.codeSeven (Fin.cons b (origin 2))) (C.codeSeven (Fin.cons b x)):=by
  apply Finset.prod_congr rfl
  intro i _
  cases hp : ps i with
  | inl bit=>cases bit <;> simp [phase,atom,P.original,OrdinaryNegativeSignedPortsCore.word,hp,P.unitPhase]
  | inr pair=>rcases pair with ⟨j,s⟩;simp [atom,OrdinaryNegativeSignedPortsCore.word,hp]

theorem phase_cross {n : ℕ} (ps : Fin n→Port 7) :
    cross (phase ps false)^2=(-1)^P.bundleSize ps 6*cross (phase ps true)^2:=by
  change cross (fun x=>∏i,atom (ps i) false x)^2=
    (-1)^P.bundleSize ps 6*cross (fun x=>∏i,atom (ps i) true x)^2
  rw [cross_prod,cross_prod,←Finset.prod_pow,←Finset.prod_pow]
  simp_rw [atom_cross]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [P.bundleSize,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases hp : ps i with
  | inl bit=>simp
  | inr pair=>
      rcases pair with ⟨j,s⟩
      by_cases hj : j=6 <;> simp [hj]

theorem phase_full {n : ℕ} (ps : Fin n→Port 7) (b : Bool) (x : Word 2) : phase ps b x≠0:=by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases hp : ps i with
  | inl bit=>exact P.unitPhase_nonzero bit
  | inr pair=>exact P.unitPhase_nonzero _

theorem incompatible {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)
    (square : Affine (fun x=>f x^2)) (masks : ∀bit,LocalAffine (pinMask f (D.ports 0) bit))
    (odd : Odd (P.bundleSize (P.port D) 6)) : False:=by
  have good (b : Bool) : Affine (fun x=>phase (P.port D) b x*slice D.reduced b x):=by
    have actual:=NoXGeneralLocalMasks.twisted_fixed D (fun x : Word 2=>Fin.cons b x)
      (cons_isAffineMap b) 0 b (fun _=>rfl) (masks b) (origin 2)
    convert actual using 1
    funext x
    rw [phase_original]
    simp only [P.original,P.unitPhase,P.word_code,slice,SystematicSupport.reduced,localTwist_apply]
  have crossed (b : Bool) : cross (phase (P.port D) b)^2*cross (slice D.reduced b)^2=1:=by
    have h:=cross_affine _ (fun x=>mul_ne_zero (phase_full _ _ _) (D.supported _)) (good b)
    rwa [cross_mul,mul_pow] at h
  have same:=parallel D.reduced D.supported (square.precompose D.encode D.affine)
  have opposite:=phase_cross (P.port D)
  rw [odd.neg_one_pow] at opposite
  have left:=crossed false
  have right:=crossed true
  rw [same,opposite] at left
  have impossible : (2 : AlgebraicComplex)=0:=by linear_combination -left-right
  norm_num at impossible

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankThreeTotalOddPhase
end
