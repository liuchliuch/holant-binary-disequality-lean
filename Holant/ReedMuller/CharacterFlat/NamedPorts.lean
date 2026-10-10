import Holant.ReedMuller.CharacterFlat.Tensor
import Holant.ReedMuller.FlatNetwork.NamedPorts
import Holant.Certificates.MatchingContractionClosure.EmptyCollection

/-! Flatness on arbitrary finite sets of named original ports. The local
contraction is identified with the existing literal assignment sum. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
variable {P : Type u} {Q : Type v}

def CharacterTensor (F : Tensor ℂ P) : Prop :=
  ∃ (n : ℕ) (e : P ≃ Fin n), NonzeroFlat (Tensor.reindex e F)

def CharacterTensorOrZero (F : Tensor ℂ P) : Prop := F=0 ∨ CharacterTensor F

theorem CharacterTensor.reindex {F : Tensor ℂ P} (hF : CharacterTensor F) (e : P ≃ Q) :
    CharacterTensor (Tensor.reindex e F) := by
  obtain ⟨n,d,h⟩ := hF
  refine ⟨n,e.symm.trans d,?_⟩
  have he : Tensor.reindex (e.symm.trans d) (Tensor.reindex e F)=Tensor.reindex d F := by
    funext x
    simp only [Tensor.reindex,Equiv.trans_apply,Equiv.symm_apply_apply]
  rwa [he]

theorem CharacterTensorOrZero.reindex {F : Tensor ℂ P} (hF : CharacterTensorOrZero F) (e : P ≃ Q) :
    CharacterTensorOrZero (Tensor.reindex e F) := by
  rcases hF with rfl | hF
  · exact Or.inl rfl
  · exact Or.inr (hF.reindex e)

theorem characterTensor_fin_iff {n : ℕ} (F : Signature ℂ n) : CharacterTensor F ↔ NonzeroFlat F := by
  constructor
  · rintro ⟨m,e,h⟩
    have H := h.reindex e.symm _
    simpa only [Tensor.reindex_symm] using H
  · intro h
    exact ⟨n,Equiv.refl _,h⟩

theorem characterTensorOrZero_fin_iff {n : ℕ} (F : Signature ℂ n) :
    CharacterTensorOrZero F ↔ CFlat F := by
  exact or_congr Iff.rfl (characterTensor_fin_iff F)

theorem characterTensorOrZero_contractPair [Fintype P] [DecidableEq P]
    (u v : P) (huv : u≠v) (eta : ZMod 2) (F : Tensor ℂ P)
    (hF : CharacterTensorOrZero F) : CharacterTensorOrZero (Holant.Certificates.MatchingContractionClosure.contractPair u v (parityKernel eta) F) := by
  let r := (Fintype.equivFin (Holant.Certificates.MatchingContractionClosure.Remaining u v)).symm
  have h := hF.reindex (pairCoordinates u v huv r).symm
  have hs := (characterTensorOrZero_fin_iff _).mp h
  have hc := hs.contract _ eta
  rw [←named_contract_coordinates u v huv r] at hc
  have hc' := (characterTensorOrZero_fin_iff _).mpr hc
  have H := hc'.reindex r
  have he : Tensor.reindex r (Tensor.reindex r.symm (Holant.Certificates.MatchingContractionClosure.contractPair u v (parityKernel eta) F))=
      Holant.Certificates.MatchingContractionClosure.contractPair u v (parityKernel eta) F := by
    funext x
    simp only [Tensor.reindex,Equiv.apply_symm_apply]
  rwa [he] at H

end
end Holant.ReedMuller.CharacterFlat
