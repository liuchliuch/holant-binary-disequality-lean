import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleSupport

/-! The two algebraic branches of the non-Product regularization lemma.
The chosen binary is still a semantic compression of an original two-bundle
pinning. No compressed signature is asserted to be physically available. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleCore
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export OrdinaryNegativeNonproductBundleSupport (Face)
end S
namespace B
export EOBinaryPlaneClassification (Full Cross full_product_iff)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ} {f : Signature AlgebraicComplex n}

def character (x y : Bool) : AlgebraicComplex := if x && y then -1 else 1

def scale (D : S.Face f) : AlgebraicComplex := D.binary ![false,false]
def first (D : S.Face f) : AlgebraicComplex := D.binary ![true,false]/scale D
def second (D : S.Face f) : AlgebraicComplex := D.binary ![false,true]/scale D

theorem scale_ne_zero (D : S.Face f) : scale D≠0 := D.full _
theorem first_ne_zero (D : S.Face f) : first D≠0 := div_ne_zero (D.full _) (scale_ne_zero D)
theorem second_ne_zero (D : S.Face f) : second D≠0 := div_ne_zero (D.full _) (scale_ne_zero D)

theorem signed_cross (D : S.Face f) :
    D.binary ![false,false]*D.binary ![true,true]=
      -(D.binary ![false,true]*D.binary ![true,false]) := by
  have hf : B.Full (fun z=>D.binary z^2) := fun z=>pow_ne_zero 2 (D.full z)
  have hh := (B.full_product_iff _ hf).mp D.square
  change D.binary ![false,false]^2*D.binary ![true,true]^2=
    D.binary ![false,true]^2*D.binary ![true,false]^2 at hh
  have hh' : (D.binary ![false,false]*D.binary ![true,true])^2=
      (D.binary ![false,true]*D.binary ![true,false])^2 := by simpa only [mul_pow] using hh
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh' with h|h
  · exact False.elim (D.nonproduct ((B.full_product_iff _ D.full).mpr h))
  · exact h

theorem formula (D : S.Face f) (z : Fin 2→Bool) :
    D.binary z=scale D*(if z 0 then first D else 1)*
      (if z 1 then second D else 1)*character (z 0) (z 1) := by
  have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
  have hc := signed_cross D
  have h0 := scale_ne_zero D
  rw [hz]
  cases h1 : z 0 <;> cases h2 : z 1
  · simp [scale,character]
  · simp [second,character]; field_simp
  · simp [first,character]; field_simp
  · simp only [Matrix.cons_val_zero,Matrix.cons_val_one,ite_true,
      character,Bool.true_and,first,second]
    simp only [mul_neg_one]
    field_simp
    dsimp [scale] at *
    linear_combination hc

/-- Positive normalization uses fifteen literal compressed evaluations, with
no inverse coefficient as a resource. The original zero-entry scale is exact. -/
def normalize (D : S.Face f) (z : Fin 2→Bool) : AlgebraicComplex :=
  D.binary z*D.binary ![z 0,false]^7*D.binary ![false,z 1]^7

theorem normalize_formula (D : S.Face f) (z : Fin 2→Bool) :
    normalize D z=scale D^15*(if z 0 then first D^8 else 1)*
      (if z 1 then second D^8 else 1)*character (z 0) (z 1) := by
  rw [normalize,formula D z,formula D ![z 0,false],formula D ![false,z 1]]
  cases z 0 <;> cases z 1 <;> simp [character] <;> ring

theorem normalize_octic (D : S.Face f) (h1 : first D^8=1) (h2 : second D^8=1)
    (z : Fin 2→Bool) : normalize D z=scale D^15*character (z 0) (z 1) := by
  rw [normalize_formula,h1,h2]
  simp

/-- Connect the second bundles of two copies, retaining both first bundles. -/
def contracted (D : S.Face f) : Signature AlgebraicComplex 2 := fun z=>
  D.binary ![z 0,false]*D.binary ![z 1,false]+
    D.binary ![z 0,true]*D.binary ![z 1,true]

theorem contracted_values (D : S.Face f) :
    contracted D ![false,false]=scale D^2*(1+second D^2) ∧
    contracted D ![false,true]=scale D^2*first D*(1-second D^2) ∧
    contracted D ![true,false]=scale D^2*first D*(1-second D^2) ∧
    contracted D ![true,true]=scale D^2*first D^2*(1+second D^2) := by
  simp only [contracted,formula]
  simp [character]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem contracted_full (D : S.Face f) (h : second D^8≠1) : B.Full (contracted D) := by
  have hp : 1+second D^2≠0 := by
    intro hz
    have hs : second D^2=-1 := by linear_combination hz
    apply h
    calc
      _=(second D^2)^4 := by ring
      _=1 := by rw [hs]; norm_num
  have hm : 1-second D^2≠0 := by
    intro hz
    have hs : second D^2=1 := by linear_combination -hz
    apply h
    calc
      _=(second D^2)^4 := by ring
      _=1 := by rw [hs]; norm_num
  intro z
  have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
  rw [hz]
  obtain ⟨h00,h01,h10,h11⟩ := contracted_values D
  cases z 0 <;> cases z 1
  · rw [h00]; exact mul_ne_zero (pow_ne_zero _ (scale_ne_zero D)) hp
  · rw [h01]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (scale_ne_zero D)) (first_ne_zero D)) hm
  · rw [h10]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (scale_ne_zero D)) (first_ne_zero D)) hm
  · rw [h11]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (scale_ne_zero D)) (pow_ne_zero _ (first_ne_zero D))) hp

theorem contracted_square_not_product (D : S.Face f) (h : second D^8≠1) :
    ¬Product (fun z=>contracted D z^2) := by
  intro hp
  have hf : B.Full (fun z=>contracted D z^2) := fun z=>pow_ne_zero _ (contracted_full D h z)
  have hh := (B.full_product_iff _ hf).mp hp
  obtain ⟨h00,h01,h10,h11⟩ := contracted_values D
  change contracted D ![false,false]^2*contracted D ![true,true]^2=
    contracted D ![false,true]^2*contracted D ![true,false]^2 at hh
  rw [h00,h01,h10,h11] at hh
  have fact : 8*scale D^8*first D^4*second D^2*(1+second D^4)=0 := by
    linear_combination hh
  have hs : 1+second D^4=0 := (mul_eq_zero.mp fact).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (scale_ne_zero D)))
      (pow_ne_zero _ (first_ne_zero D))) (pow_ne_zero _ (second_ne_zero D)))
  have hs' : second D^4=-1 := by linear_combination hs
  apply h
  calc
    _=(second D^4)^2 := by ring
    _=1 := by rw [hs']; norm_num

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleCore
end
