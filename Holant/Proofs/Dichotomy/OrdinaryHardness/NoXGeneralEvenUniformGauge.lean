import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniform
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSystematicSupport

/-! Even total character multiplicities make the uniform input twist an
invertible Affine gauge on the actual support. Both Affine and LocalAffine
membership therefore survive that semantic twist. No physical gauge is added. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenUniformGauge
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace G
export OrdinaryNegativeSignedRowsUniform (gauge gauge_affine gauge_ne_zero count phase read)
export OrdinaryNegativeAffineSquareReciprocal (affine_inverse)
export OrdinaryNegativeAffineRankOne (uniform)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n r m : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
variable (ps : Fin n→Port m) (code : Word r→Word m)
variable (codeAffine : IsAffineMap code)
variable (chart : ∀x,word ps (code x)=D.encode x)
variable (even : ∀j,Even (OrdinaryNegativeSignedPortsIncidence.bundleSize ps j))

def coordinates (x : Word n) : Word m := code (fun j=>x (D.ports j))
def fullGauge : Signature AlgebraicComplex n := fun x=>G.gauge ps (coordinates D code x)

include codeAffine in
theorem coordinates_affine : IsAffineMap (coordinates D code) := by
  intro x y
  exact codeAffine (fun j=>x (D.ports j)) (fun j=>y (D.ports j))

include codeAffine even in
theorem gauge_affine : Affine (fullGauge D ps code) := by
  have counts : ∀j,Even (G.count ps j) := fun j=>even j
  exact (G.gauge_affine ps counts).precompose (coordinates D code) (coordinates_affine D code codeAffine)

theorem gauge_full (x : Word n) : fullGauge D ps code x≠0 := G.gauge_ne_zero ps _

include chart in
theorem value : G.uniform f=(fun x=>fullGauge D ps code x*f x) := by
  funext x
  by_cases hx : f x=0
  · simp only [G.uniform,localTwist_apply,hx,mul_zero]
  · have actual : word ps (coordinates D code x)=x :=
      (chart (fun j=>x (D.ports j))).trans (D.covers x hx)
    have read_eq (i : Fin n) : G.read (ps i) (coordinates D code x)=x i := by
      have h:=congrFun actual i
      cases hp : ps i with
      | inl b=>simpa only [G.read,OrdinaryNegativeSignedPortsCore.word,hp] using h
      | inr pair=>rcases pair with ⟨j,b⟩;simpa only [G.read,OrdinaryNegativeSignedPortsCore.word,hp] using h
    simp only [G.uniform,localTwist_apply,Bool.true_and,fullGauge,G.gauge,read_eq,G.phase]

include codeAffine chart even in
theorem affine_iff : Affine (G.uniform f) ↔ Affine f := by
  rw [value D ps code chart]
  constructor
  · intro h
    convert (G.affine_inverse _ (gauge_affine D ps code codeAffine even)).mul h using 1
    funext x
    rw [←mul_assoc,inv_mul_cancel₀ (gauge_full D ps code x),one_mul]
  · intro h
    exact (gauge_affine D ps code codeAffine even).mul h

section Local
variable {k : ℕ} (g h : Signature AlgebraicComplex k) (affine : Affine g) (full : ∀x,g x≠0)
include affine full in
theorem local_mul_iff : LocalAffine (fun x=>g x*h x) ↔ LocalAffine h := by
  constructor
  · intro hlocal a ha
    have good:=hlocal a (mul_ne_zero (full a) ha)
    have product := (G.affine_inverse _ affine).mul good
    convert product using 1
    funext x
    rw [localTwist_apply,localTwist_apply]
    field_simp [full x]
  · intro hlocal a ha
    have good:=affine.mul (hlocal a (mul_ne_zero_iff.mp ha).2)
    convert good using 1
    funext x
    simp only [localTwist_apply]
    ring
end Local

include codeAffine chart even in
theorem local_iff : LocalAffine (G.uniform f) ↔ LocalAffine f := by
  rw [value D ps code chart]
  exact local_mul_iff _ _ (gauge_affine D ps code codeAffine even) (gauge_full D ps code)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenUniformGauge
end
