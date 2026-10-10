import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSubstitution
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionWeight
import Holant.Proofs.Hardness.EOMixedBinaryLocal

/-! Internally chosen weighted interaction for the unequal-fourth-power,
intersection-closed branch. The resulting full binary is outside both literal
classes and is a product of at most two actual constant/identification minors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionInteraction
open Holant Holant.Tractable Function
open GeneralEOPairedFamilyExtractionSupport
namespace C
export GeneralEOPairedFamilyExtractionComponentsFull (reduced substitution expand_substitute exists_nonproduct_face)
end C
namespace W
export GeneralEOPairedFamilyExtractionWeight (CommonFourthSupport exists_weight)
end W
namespace B
export EOBinaryPlaneClassification (Full)
end B
namespace L
export EOMixedBinaryLocal (weighted weighted_full weighted_not_affine weighted_not_product)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable

variable {m n k : ℕ}


variable (f : Signature AlgebraicComplex n) (h0 : f origin≠0) (hx : XorClosed f)
variable (hm : MeetClosed f) (hp : ¬Product f)

include h0 hx hm hp in
theorem exists_interaction :
    ∃p : Fin n → Bool ⊕ Fin 2,
      B.Full (fun z => f (T.substitute p z)) ∧ ¬Product (fun z => f (T.substitute p z)) := by
  obtain ⟨i,j,_,x,hfull,hprod⟩ := C.exists_nonproduct_face f h0 hx hm hp
  have he : (fun z => f (T.substitute (compose (C.substitution f) (facePorts i j x)) z))=
      GeneralEOPairedFamilyExtractionFullSupport.face (C.reduced f) i j x := by
    funext z
    rw [substitute_compose]
    rw [←C.expand_substitute]
    exact face_substitute (C.reduced f) i j x z
  refine ⟨compose (C.substitution f) (facePorts i j x),?_,?_⟩
  · rwa [he]
  · rwa [he]

def interactionPorts := Classical.choose (exists_interaction f h0 hx hm hp)
def interaction : Signature AlgebraicComplex 2 := fun z => f (T.substitute (interactionPorts f h0 hx hm hp) z)

theorem interaction_spec : B.Full (interaction f h0 hx hm hp) ∧ ¬Product (interaction f h0 hx hm hp) :=
  Classical.choose_spec (exists_interaction f h0 hx hm hp)

variable (hw : ¬W.CommonFourthSupport f)

def weightWord := Classical.choose (W.exists_weight f h0 hw)

def weightPorts : Fin n → Bool ⊕ Fin 2 := fun i => if weightWord f h0 hw i then Sum.inr 0 else Sum.inl false

theorem weight_minor (z : Fin 2 → Bool) :
    f (T.substitute (weightPorts f h0 hw) z)=if z 0 then f (weightWord f h0 hw) else f origin := by
  cases h : z 0 with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply congrArg f
    funext i
    cases hi : weightWord f h0 hw i <;> simp [T.substitute,weightPorts,origin,hi,h]
  | true =>
    simp only [ite_true]
    apply congrArg f
    funext i
    cases hi : weightWord f h0 hw i <;> simp [T.substitute,weightPorts,hi,h]

def hardPorts : List (Fin n → Bool ⊕ Fin 2) :=
  if Affine (interaction f h0 hx hm hp) then
    [weightPorts f h0 hw,interactionPorts f h0 hx hm hp]
  else [interactionPorts f h0 hx hm hp]

def hardBinary : Signature AlgebraicComplex 2 := fun z =>
  ((hardPorts f h0 hx hm hp hw).map (fun p => f (T.substitute p z))).prod

theorem hard_ports_length : (hardPorts f h0 hx hm hp hw).length≤2 := by
  unfold hardPorts
  split_ifs <;> simp

theorem hard_spec : B.Full (hardBinary f h0 hx hm hp hw) ∧
    ¬Affine (hardBinary f h0 hx hm hp hw) ∧ ¬Product (hardBinary f h0 hx hm hp hw) := by
  obtain ⟨hfull,hprod⟩ := interaction_spec f h0 hx hm hp
  have hweight := Classical.choose_spec (W.exists_weight f h0 hw)
  by_cases ha : Affine (interaction f h0 hx hm hp)
  · have he : hardBinary f h0 hx hm hp hw=L.weighted (interaction f h0 hx hm hp)
        (f (weightWord f h0 hw)) (f origin) := by
      funext z
      simp only [hardBinary,hardPorts,ha,ite_true,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
      rw [weight_minor f h0 hw z]
      rfl
    rw [he]
    exact ⟨L.weighted_full _ _ _ hfull hweight.1 h0,
      L.weighted_not_affine _ _ _ hfull ha hweight.1 h0 hweight.2.1,
      L.weighted_not_product _ _ _ hfull hprod hweight.1 h0⟩
  · have he : hardBinary f h0 hx hm hp hw=interaction f h0 hx hm hp := by
      funext z
      simp only [hardBinary,hardPorts,ha,ite_false,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
      rfl
    rw [he]
    exact ⟨hfull,ha,hprod⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionInteraction
