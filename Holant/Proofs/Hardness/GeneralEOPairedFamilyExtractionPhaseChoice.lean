import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseBundle
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseTrace

/-! An arbitrary full-support, equal-fourth-power, nonaffine signature
internally supplies either a hard binary literal face or a nontrivial ternary
monomial represented by an actual fixed product of its literal minors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseChoice
open Holant Holant.Tractable
open GeneralEOPairedFamilyExtractionPhaseNormalization
namespace A
export AffinePhase (word basis origin)
end A
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate evaluate_scale evaluate_compose ports ports_value)
end B
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose)
end I
namespace P
export EOBinaryPlaneClassification (Full Cross full_affine_iff full_product_iff)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def pairPorts (e : Edge n) : Fin n → Bool ⊕ Fin 2 :=
  fun j => if j=e.val.1 then Sum.inr 0 else if j=e.val.2 then Sum.inr 1 else Sum.inl false

theorem pair_word (e : Edge n) (z : Fin 2 → Bool) : T.substitute (pairPorts e) z=
    if z 0 then (if z 1 then A.word {e.val.1,e.val.2} else A.basis e.val.1)
    else (if z 1 then A.basis e.val.2 else A.origin n) := by
  have hn : e.val.1≠e.val.2 := ne_of_lt e.property
  funext j
  by_cases ha : j=e.val.1
  · subst j
    cases h0 : z 0 <;> cases h1 : z 1 <;> simp [T.substitute,pairPorts,A.word,A.basis,A.origin,h0,hn]
  · by_cases hb : j=e.val.2
    · subst j
      cases h0 : z 0 <;> cases h1 : z 1 <;> simp [T.substitute,pairPorts,A.word,A.basis,A.origin,h1,ha]
    · cases h0 : z 0 <;> cases h1 : z 1 <;> simp [T.substitute,pairPorts,A.word,A.basis,A.origin,ha,hb]

theorem pair_value (g : Signature AlgebraicComplex n) (h0 : g (A.origin n)=1)
    (e : Edge n) (z : Fin 2 → Bool) : g (T.substitute (pairPorts e) z)=pairTable g e z := by
  rw [pair_word]
  cases h0' : z 0 <;> cases h1 : z 1 <;> simp [pairTable,h0',h1,h0]

variable (f : Signature AlgebraicComplex n)

def normalized : Signature AlgebraicComplex n := fun x => (f (A.origin n))⁻¹*f x

variable (hf : ∀x,f x≠0) (ha : ¬Affine f)
variable (hpow : ∀x,f x^4=f (A.origin n)^4)

include hf in
theorem normalized_origin : normalized f (A.origin n)=1 := by
  exact inv_mul_cancel₀ (hf _)

include hf hpow in
theorem normalized_four (x : Fin n → Bool) : normalized f x^4=1 := by
  rw [normalized,mul_pow,inv_pow,hpow x,inv_mul_cancel₀ (pow_ne_zero 4 (hf _))]

include hf ha in
theorem normalized_not_affine : ¬Affine (normalized f) := by
  intro h
  apply ha
  convert h.scale (f (A.origin n)) using 1
  funext x
  simp only [normalized,←mul_assoc,mul_inv_cancel₀ (hf _),one_mul]

include hf in
theorem denormalize : f=(fun x => f (A.origin n)*normalized f x) := by
  funext x
  simp only [normalized,←mul_assoc,mul_inv_cancel₀ (hf _),one_mul]

include hf ha hpow in
theorem alternatives :
    (∃p : Fin n → Bool ⊕ Fin 2,
      P.Full (fun z => f (T.substitute p z)) ∧
        ¬Affine (fun z => f (T.substitute p z)) ∧ ¬Product (fun z => f (T.substitute p z))) ∨
    (∃ps : List (Fin n → Bool ⊕ Fin 3),∃c δ : AlgebraicComplex,
      c≠0 ∧ δ^4=1 ∧ δ≠1 ∧
        ∀z : Fin 3 → Bool,B.evaluate f ps z=c*(if z=![true,true,true] then δ else 1)) := by
  by_cases hp : ∀e : Edge n,Affine (pairTable (normalized f) e)
  · right
    obtain ⟨p,δ,hδ,hn,he⟩ := GeneralEOPairedFamilyExtractionPhaseSmall.exists_ternary
      (normalized f) (normalized_origin f hf) (normalized_four f hf hpow)
      (normalized_not_affine f hf ha) hp
    let ps := B.ports.map (fun q => I.compose q p)
    refine ⟨ps,f (A.origin n)^ps.length,δ,pow_ne_zero _ (hf _),hδ,hn,?_⟩
    intro z
    have hs := B.evaluate_scale (normalized f) (f (A.origin n)) ps z
    rw [←denormalize f hf] at hs
    rw [hs]
    change _*B.evaluate (normalized f) (B.ports.map (fun q => I.compose q p)) z=_
    rw [B.evaluate_compose,B.ports_value (normalized f) (normalized_origin f hf)
      (normalized_four f hf hpow),he]
  · left
    obtain ⟨e,he⟩ := not_forall.mp hp
    have hfull : P.Full (pairTable (normalized f) e) := by
      intro z hz
      have hh := normalized_four f hf hpow (T.substitute (pairPorts e) z)
      rw [pair_value _ (normalized_origin f hf),hz] at hh
      norm_num at hh
    have hprod : ¬Product (pairTable (normalized f) e) := by
      intro hh
      apply he
      apply (P.full_affine_iff _ hfull).mpr
      refine ⟨?_,Or.inl ((P.full_product_iff _ hfull).mp hh)⟩
      intro z
      rw [←pair_value _ (normalized_origin f hf) e z,
        ←pair_value _ (normalized_origin f hf) e ![false,false],normalized_four f hf hpow,
        normalized_four f hf hpow]
    refine ⟨pairPorts e,fun z => hf _,?_,?_⟩
    · intro hh
      have h := hh.scale ((f (A.origin n))⁻¹)
      have eq : (fun z => (f (A.origin n))⁻¹*f (T.substitute (pairPorts e) z))=
          pairTable (normalized f) e := funext (pair_value _ (normalized_origin f hf) e)
      exact he (eq ▸ h)
    · intro hh
      have h := hh.scale ((f (A.origin n))⁻¹)
      have eq : (fun z => (f (A.origin n))⁻¹*f (T.substitute (pairPorts e) z))=
          pairTable (normalized f) e := funext (pair_value _ (normalized_origin f hf) e)
      exact hprod (eq ▸ h)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseChoice
