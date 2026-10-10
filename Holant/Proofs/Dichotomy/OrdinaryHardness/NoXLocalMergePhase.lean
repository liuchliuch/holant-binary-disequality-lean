import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalAffineCubeControls
import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorAffine

/-! Exact local-twist transport for the actual Eq4 equality merge and its
weighted-antidiagonal opposite merge. Only a supported marker is needed;
no full-support or freely available merged row is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalMergePhase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ}
def flip (x : Word (n+2)) : Word (n+2) := Fin.cons (!(x 0)) (fun i=>x i.succ)
@[simp] theorem flip_zero (x : Word (n+2)) : flip x 0=!(x 0) := rfl
@[simp] theorem flip_one (x : Word (n+2)) : flip x 1=x 1 := rfl
@[simp] theorem flip_succ (x : Word (n+2)) (i : Fin (n+1)) : flip x i.succ=x i.succ := rfl
@[simp] theorem flip_flip (x : Word (n+2)) : flip (flip x)=x := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [flip]
  · rfl

theorem flip_affine : TwoTranslate.IsAffineMap (flip (n:=n)) := by
  intro x y
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change (Bool.not ((x 0) ^^ (y 0)))=((Bool.not (x 0)) ^^ ((Bool.not (y 0)) ^^ true))
    cases x 0 <;> cases y 0 <;> rfl
  · change (x j.succ ^^ y j.succ)=(x j.succ ^^ (y j.succ ^^ false))
    simp

def equal (f : Signature AlgebraicComplex (n+2)) : Signature AlgebraicComplex (n+2) :=
  fun x=>if x 0=x 1 then f x else 0
def unequal (f : Signature AlgebraicComplex (n+2)) : Signature AlgebraicComplex (n+2) :=
  fun x=>if x 0≠x 1 then f x else 0
def opposite (f : Signature AlgebraicComplex (n+2)) (v w : AlgebraicComplex) : Signature AlgebraicComplex (n+2) :=
  fun x=>if x 0=x 1 then (if x 0 then v else w)*f (flip x) else 0

theorem equal_twist (f : Signature AlgebraicComplex (n+2)) (a : Word (n+2)) :
    localTwist a (equal f)=equal (localTwist a f) := by
  funext x
  by_cases h : x 0=x 1 <;> simp [localTwist_apply,equal,h]

theorem equal_of_local (f : Signature AlgebraicComplex (n+2)) (a : Word (n+2))
    (supported : f a≠0) (same : a 0=a 1) (locality : LocalAffine (equal f)) :
    Affine (equal (localTwist a f)) := by
  rw [←equal_twist]
  exact locality a (by simpa [equal,same] using supported)

def zeroCoeff (a : Word (n+2)) (v _w : AlgebraicComplex) : AlgebraicComplex :=
  if a 0 then v else zetaEight*v
def oneCoeff (a : Word (n+2)) (_v w : AlgebraicComplex) : AlgebraicComplex :=
  if a 0 then w/zetaEight else w
def coeff (a : Word (n+2)) (v w : AlgebraicComplex) (b : Bool) : AlgebraicComplex :=
  if b then oneCoeff a v w else zeroCoeff a v w

theorem coeff_nonzero (a : Word (n+2)) (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0) (b : Bool) :
    coeff a v w b≠0 := by
  cases ha : a 0 <;> cases b <;> simp [coeff,zeroCoeff,oneCoeff,ha,hv,hw,zetaEight_ne_zero]

theorem coeff_fourth (a : Word (n+2)) (v w : AlgebraicComplex) (fourth : v^4= -(w^4)) :
    zeroCoeff a v w^4=oneCoeff a v w^4 := by
  cases ha : a 0 <;> simp [zeroCoeff,oneCoeff,ha,mul_pow,div_pow,zetaEight_pow_four,
    fourth,div_neg,div_one]

theorem inverse_coeff_affine (a : Word (n+2)) (v w : AlgebraicComplex)
    (hv : v≠0) (hw : w≠0) (fourth : v^4= -(w^4)) :
    Affine (fun x : Word (n+2)=>(coeff a v w (x 0))⁻¹) := by
  have h0 : zeroCoeff a v w≠0 := coeff_nonzero a v w hv hw false
  have he : (zeroCoeff a v w)⁻¹^4=(oneCoeff a v w)⁻¹^4 := by
    rw [inv_pow,inv_pow,coeff_fourth a v w fourth]
  have h := GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers (0 : Fin (n+2))
    (zeroCoeff a v w)⁻¹ (oneCoeff a v w)⁻¹ (inv_ne_zero h0) he
  convert h using 1
  funext x
  cases x 0 <;> rfl

theorem opposite_twisted (f : Signature AlgebraicComplex (n+2)) (a x : Word (n+2)) (v w : AlgebraicComplex) :
    localTwist (flip a) (opposite f v w) (flip x)=
      coeff a v w (x 0)*unequal (localTwist a f) x := by
  simp only [localTwist_apply,Fin.prod_univ_succ,flip_zero,flip_one,flip_succ,opposite,flip_flip,unequal,coeff,zeroCoeff,oneCoeff]
  rcases Bool.eq_false_or_eq_true (a 0) with ha|ha <;>
    rcases Bool.eq_false_or_eq_true (x 0) with hx|hx <;>
    rcases Bool.eq_false_or_eq_true (x 1) with h1|h1 <;>
    simp [ha,hx,h1]
  all_goals field_simp [zetaEight_ne_zero]

theorem opposite_of_local (f : Signature AlgebraicComplex (n+2)) (a : Word (n+2))
    (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0) (fourth : v^4= -(w^4))
    (supported : f a≠0) (different : a 0≠a 1) (locality : LocalAffine (opposite f v w)) :
    Affine (unequal (localTwist a f)) := by
  have relation : flip a 0=flip a 1 := by
    change (Bool.not (a 0))=a 1
    have eqn : ∀b c : Bool,b≠c→Bool.not b=c := by decide
    exact eqn _ _ different
  have selected : opposite f v w (flip a)≠0 := by
    simp only [opposite,ite_eq_left relation,flip_flip]
    apply mul_ne_zero _ supported
    cases flip a 0 <;> assumption
  have hA := (locality (flip a) selected).precompose flip flip_affine
  have h := (inverse_coeff_affine a v w hv hw fourth).mul hA
  convert h using 1
  funext x
  rw [opposite_twisted]
  rw [←mul_assoc,inv_mul_cancel₀ (coeff_nonzero a v w hv hw _),one_mul]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalMergePhase
end
