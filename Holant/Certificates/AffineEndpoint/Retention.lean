import Holant.Certificates.AffineEndpoint.BaseTransform

/-! Exact Boolean retention checks correspond to the actual output support,
including every forbidden odd word and both nonzero endpoints. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor IntegerValues
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def IntegerRetained (c : InputCode) (k : Fin 18) : Prop :=
  integerOutput c k 0≠zero ∧ integerOutput c k 15≠zero ∧
    ∀i : Fin 8,integerOutput c k (oddCode i)=zero

 instance (c : InputCode) (k : Fin 18) : Decidable (IntegerRetained c k) := by unfold IntegerRetained; infer_instance

 theorem oddCode_complete : ∀x : Fin 4 → Bool,Holant.weight x%2=1→∃i : Fin 8,x=codeWord (oddCode i) := by decide +kernel

 theorem integerRetained_iff_cleared (c : InputCode) (k : Fin 18) :
    IntegerRetained c k ↔ EndpointEven (clearedOutput c k) := by
  have ho (x : Fin 16) := clearedOutput_code c k x
  have h0 : alg (integerOutput c k 0)=clearedOutput c k zeroWord :=
    (ho 0).trans (congrArg _ zeroCode_word)
  have h1 : alg (integerOutput c k 15)=clearedOutput c k oneWord :=
    (ho 15).trans (congrArg _ oneCode_word)
  constructor
  · rintro ⟨hr0,hr1,hro⟩
    refine ⟨fun hz => alg_ne_zero hr0 (h0.trans hz),fun hz => alg_ne_zero hr1 (h1.trans hz),?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := oddCode_complete x hx
    exact (ho _).symm.trans (by rw [hro i,alg_zero])
  · rintro ⟨hr0,hr1,hro⟩
    refine ⟨fun hz => hr0 (h0.symm.trans (by rw [hz,alg_zero])),
      fun hz => hr1 (h1.symm.trans (by rw [hz,alg_zero])),?_⟩
    intro i
    apply alg_injective
    exact (ho _).trans ((hro _ (oddCode_weight i)).trans alg_zero.symm)

 theorem integerRetained_iff (c : InputCode) (k : Fin 18) :
    IntegerRetained c k ↔ EndpointEven (Signature.coordinateAction
      (fun _ => coreMatrix (numberedCore k)) (inputSignature c)) := by
  rw [integerRetained_iff_cleared,clearedOutput_eq]
  exact endpointEven_scale_iff _ _ (pow_ne_zero 4 (algebraicEmbed_ne_zero (coreClearingScale_ne_zero k)))

 def BaseRetained (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) : Prop :=
  baseIntegerOutput s c b 0≠zero ∧ baseIntegerOutput s c b 15≠zero ∧
    ∀i : Fin 8,baseIntegerOutput s c b (oddCode i)=zero

 instance (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool) : Decidable (BaseRetained s c b) := by
  unfold BaseRetained; infer_instance

 theorem baseRetained_iff (c : InputCode) (b : Bool) :
    BaseRetained c.1 c.2.val b ↔ IntegerRetained c (baseCore b) := by
  simp only [BaseRetained,IntegerRetained,baseIntegerOutput_eq,fastIntegerOutput_eq]

 theorem baseRetained_sound (c : InputCode) (b : Bool) (h : BaseRetained c.1 c.2.val b) :
    EndpointEven (Signature.coordinateAction (fun _ => coreMatrix (numberedCore (baseCore b))) (inputSignature c)) :=
  (integerRetained_iff c (baseCore b)).mp ((baseRetained_iff c b).mp h)

end
end Holant.Certificates.AffineEndpoint
