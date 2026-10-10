import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionParity

/-! Actual nonaffine unary extraction from unequal support fourth powers.
The source word is chosen internally and all of its true coordinates are
identified. Only the false reserved constant is used. Sparse support and
arbitrary original arities are allowed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionWeight
open Computability Holant Holant.Tractable Holant.Complexity
open GeneralEOPairedFamilyExtractionSupport
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed extracted)
end E
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace S
export GeneralEOPairedFamilyExtractionRestrictionSource
  (chosenLeft chosenRight coefficient coefficient_exact selectedValue originalSource)
end S
namespace B
export GeneralEOPairedFamilyExtractionOrigin (extracted_origin)
end B
namespace P
export GeneralEOPairedCSPFamilyFieldClosed (pairing)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalValue originalPresentation)
end O
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}

def CommonFourthSupport (f : Signature AlgebraicComplex n) : Prop :=
  ∀x,f x≠0 → f x^4=f origin^4

def weightPorts (u : Fin n → Bool) : Fin n → Bool ⊕ Fin 1 :=
  fun i => if u i then Sum.inr 0 else Sum.inl false

def weight (f : Signature AlgebraicComplex n) (u : Fin n → Bool) :
    Signature AlgebraicComplex 1 := fun z => f (T.substitute (weightPorts u) z)

theorem weight_false (f : Signature AlgebraicComplex n) (u : Fin n → Bool) :
    weight f u ![false]=f origin := by
  apply congrArg f
  funext i
  cases h : u i <;> simp [T.substitute,weightPorts,origin,h]

theorem weight_true (f : Signature AlgebraicComplex n) (u : Fin n → Bool) :
    weight f u ![true]=f u := by
  apply congrArg f
  funext i
  cases h : u i <;> simp [T.substitute,weightPorts,h]

theorem weight_full (f : Signature AlgebraicComplex n) (u : Fin n → Bool)
    (h0 : f origin≠0) (hu : f u≠0) : ∀z,weight f u z≠0 := by
  intro z
  have hz : z=![z 0] := by funext i; fin_cases i; rfl
  rw [hz]
  cases z 0
  · simpa only [weight_false] using h0
  · simpa only [weight_true] using hu

theorem weight_not_affine (f : Signature AlgebraicComplex n) (u : Fin n → Bool)
    (h0 : f origin≠0) (hu : f u≠0) (hne : f u^4≠f origin^4) :
    ¬Affine (weight f u) := by
  intro h
  have hh := h.fourth_power_eq ![true] ![false]
    (weight_full f u h0 hu _) (weight_full f u h0 hu _)
  rw [weight_true,weight_false] at hh
  exact hne hh

/-- Unequal literal support powers select a genuine full unary minor. -/
theorem exists_weight (f : Signature AlgebraicComplex n) (h0 : f origin≠0)
    (hn : ¬CommonFourthSupport f) :
    ∃u : Fin n → Bool,f u≠0 ∧ f u^4≠f origin^4 ∧
      (∀z,weight f u z≠0) ∧ ¬Affine (weight f u) := by
  unfold CommonFourthSupport at hn
  push Not at hn
  obtain ⟨u,hu,hne⟩ := hn
  exact ⟨u,hu,hne,weight_full f u h0 hu,weight_not_affine f u h0 hu hne⟩

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))
variable (hw : ¬CommonFourthSupport (E.extracted G he hn hc ha hp))

def chosenWord := Classical.choose (exists_weight (E.extracted G he hn hc ha hp)
  (B.extracted_origin G he hn hc ha hp) hw)

def chosenPorts := weightPorts (chosenWord G he hn hc ha hp hw)

abbrev unaryValue := S.selectedValue G he hn hc ha hp (chosenPorts G he hn hc ha hp hw)

def unarySource :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (unaryValue G he hn hc ha hp hw) (O.originalValue G) :=
  S.originalSource G he hn hc ha hp (chosenPorts G he hn hc ha hp hw)

theorem unary_coefficient (z : Fin 1 → Bool) :
    (S.coefficient G (P.pairing G he hn hc)
      (S.chosenLeft G he hn hc ha) (S.chosenRight G he hn hc hp)
      (chosenPorts G he hn hc ha hp hw) z : AlgebraicComplex)=
        weight (E.extracted G he hn hc ha hp) (chosenWord G he hn hc ha hp hw) z :=
  S.coefficient_exact G he hn hc ha hp (chosenPorts G he hn hc ha hp hw) z

theorem unary_spec :
    (∀z,weight (E.extracted G he hn hc ha hp) (chosenWord G he hn hc ha hp hw) z≠0) ∧
      ¬Affine (weight (E.extracted G he hn hc ha hp) (chosenWord G he hn hc ha hp hw)) ∧
      weight (E.extracted G he hn hc ha hp) (chosenWord G he hn hc ha hp hw) ![true]^4≠
        weight (E.extracted G he hn hc ha hp) (chosenWord G he hn hc ha hp hw) ![false]^4 := by
  have h := Classical.choose_spec (exists_weight (E.extracted G he hn hc ha hp)
    (B.extracted_origin G he hn hc ha hp) hw)
  refine ⟨h.2.2.1,h.2.2.2,?_⟩
  simpa only [weight_true,weight_false,chosenWord] using h.2.1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionWeight
