import Holant.Certificates.AffineEndpoint.ScaledInputs
import Holant.Certificates.AffineEndpoint.InputUniqueness

/-! Projective affine automorphisms induce genuine permutations of the
canonically normalized inputs. The normalization scalar is retained explicitly. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.AffineEndpoint
open SupportCatalog
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev Sig := Signature AlgebraicComplex 4

theorem input_scaled_injective (c d : InputCode) (a b : AlgebraicComplex)
    (ha : a ≠ 0) (hb : b ≠ 0) (he : a • inputSignature c = b • inputSignature d) : c = d := by
  have hs (x : Fin 4 → Bool) : inputSignature c x ≠ 0 ↔ inputSignature d x ≠ 0 := by
    have h := congrFun he x
    change a * inputSignature c x = b * inputSignature d x at h
    constructor
    · intro hc hd
      rw [hd,mul_zero] at h
      exact mul_ne_zero ha hc h
    · intro hd hc
      rw [hc,mul_zero] at h
      exact mul_ne_zero hb hd h.symm
  have h0 : inputSignature d (supportOrigin c.1) = 1 :=
    inputSignature_normalized d _ ((hs _).mp (by rw [inputSignature_origin]; exact one_ne_zero))
      (fun x hx => supportOrigin_least c.1 x ((inputSignature_support c x).mp ((hs x).mpr hx)))
  have hab := congrFun he (supportOrigin c.1)
  simp only [Pi.smul_apply,smul_eq_mul,inputSignature_origin,h0,mul_one] at hab
  subst b
  apply inputSignature_injective
  funext x
  exact mul_left_cancel₀ ha (congrFun he x)

structure ProjectiveAffineMap where
  toFun : Sig → Sig
  scale : ∀(a : AlgebraicComplex) (f : Sig), toFun (a • f) = a • toFun f
  affine : ∀f, Affine f → Affine (toFun f)
  nonzero : ∀f, f ≠ 0 → toFun f ≠ 0

namespace ProjectiveAffineMap

theorem outputCode_exists (T : ProjectiveAffineMap) (c : InputCode) :
    ∃d : InputCode,∃a : AlgebraicComplex,a ≠ 0 ∧ T.toFun (inputSignature c) = a • inputSignature d := by
  obtain ⟨a,ha,d,hd⟩ := scaled_input_coverage _ (T.affine _ (inputSignature_affine c))
    (T.nonzero _ (inputSignature_ne_zero c))
  exact ⟨d,a,ha,hd⟩

def outputCode (T : ProjectiveAffineMap) (c : InputCode) : InputCode :=
  Classical.choose (outputCode_exists T c)

theorem outputCode_spec (T : ProjectiveAffineMap) (c : InputCode) :
    ∃a : AlgebraicComplex,a ≠ 0 ∧ T.toFun (inputSignature c) = a • inputSignature (T.outputCode c) :=
  Classical.choose_spec (outputCode_exists T c)

def comp (T U : ProjectiveAffineMap) : ProjectiveAffineMap where
  toFun := fun f => T.toFun (U.toFun f)
  scale := by intro a f; rw [U.scale,T.scale]
  affine := fun f hf => T.affine _ (U.affine _ hf)
  nonzero := fun f hf => T.nonzero _ (U.nonzero _ hf)

theorem outputCode_comp (T U : ProjectiveAffineMap) (c : InputCode) :
    (T.comp U).outputCode c = T.outputCode (U.outputCode c) := by
  obtain ⟨a,ha,hea⟩ := U.outputCode_spec c
  obtain ⟨b,hb,heb⟩ := T.outputCode_spec (U.outputCode c)
  obtain ⟨d,hd,hed⟩ := (T.comp U).outputCode_spec c
  apply input_scaled_injective _ _ d (a*b) hd (mul_ne_zero ha hb)
  rw [←hed]
  change T.toFun (U.toFun (inputSignature c)) = _
  rw [hea,T.scale,heb,smul_smul]

theorem outputCode_scalar (T : ProjectiveAffineMap) (a : AlgebraicComplex) (ha : a ≠ 0)
    (he : ∀f,T.toFun f = a • f) (c : InputCode) : T.outputCode c = c := by
  obtain ⟨b,hb,hbval⟩ := T.outputCode_spec c
  apply input_scaled_injective _ _ b a hb ha
  rw [←hbval,he]

end ProjectiveAffineMap

structure ProjectiveAffineAutomorphism where
  forward : ProjectiveAffineMap
  backward : ProjectiveAffineMap
  backward_forward : ∃a : AlgebraicComplex,a ≠ 0 ∧ ∀f,backward.toFun (forward.toFun f) = a • f
  forward_backward : ∃a : AlgebraicComplex,a ≠ 0 ∧ ∀f,forward.toFun (backward.toFun f) = a • f

namespace ProjectiveAffineAutomorphism

def inputEquiv (T : ProjectiveAffineAutomorphism) : InputCode ≃ InputCode where
  toFun := T.forward.outputCode
  invFun := T.backward.outputCode
  left_inv c := by
    rw [←ProjectiveAffineMap.outputCode_comp]
    obtain ⟨a,ha,he⟩ := T.backward_forward
    exact ProjectiveAffineMap.outputCode_scalar _ a ha he c
  right_inv c := by
    rw [←ProjectiveAffineMap.outputCode_comp]
    obtain ⟨a,ha,he⟩ := T.forward_backward
    exact ProjectiveAffineMap.outputCode_scalar _ a ha he c

theorem inputEquiv_spec (T : ProjectiveAffineAutomorphism) (c : InputCode) :
    ∃a : AlgebraicComplex,a ≠ 0 ∧ T.forward.toFun (inputSignature c) = a • inputSignature (T.inputEquiv c) :=
  T.forward.outputCode_spec c

end ProjectiveAffineAutomorphism
end
end Holant.Certificates.AffineEndpointCounts
