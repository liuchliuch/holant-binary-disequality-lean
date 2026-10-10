import Holant.ReedMuller.FlatNetwork.Tensor
import Holant.Certificates.MatchingContractionClosure.EmptyCollection

/-! Flatness on arbitrary finite sets of named original ports. The local
contraction is identified with the existing literal assignment sum. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
variable {P : Type u} {Q : Type v}

def FlatTensor (F : Tensor ℂ P) : Prop :=
  ∃ (n : ℕ) (e : P ≃ Fin n), Flat (Tensor.reindex e F)

def FlatTensorOrZero (F : Tensor ℂ P) : Prop := F=0 ∨ FlatTensor F

theorem FlatTensor.reindex {F : Tensor ℂ P} (hF : FlatTensor F) (e : P ≃ Q) :
    FlatTensor (Tensor.reindex e F) := by
  obtain ⟨n,d,h⟩ := hF
  refine ⟨n,e.symm.trans d,?_⟩
  have he : Tensor.reindex (e.symm.trans d) (Tensor.reindex e F)=Tensor.reindex d F := by
    funext x
    simp only [Tensor.reindex,Equiv.trans_apply,Equiv.symm_apply_apply]
  rwa [he]

theorem FlatTensorOrZero.reindex {F : Tensor ℂ P} (hF : FlatTensorOrZero F) (e : P ≃ Q) :
    FlatTensorOrZero (Tensor.reindex e F) := by
  rcases hF with rfl | hF
  · exact Or.inl rfl
  · exact Or.inr (hF.reindex e)

theorem flatTensor_fin_iff {n : ℕ} (F : Signature ℂ n) : FlatTensor F ↔ Flat F := by
  constructor
  · rintro ⟨m,e,h⟩
    have H := flat_reindex e.symm _ h
    simpa only [Tensor.reindex_symm] using H
  · intro h
    exact ⟨n,Equiv.refl _,h⟩

theorem flatTensorOrZero_fin_iff {n : ℕ} (F : Signature ℂ n) :
    FlatTensorOrZero F ↔ FlatOrZero F := by
  exact or_congr Iff.rfl (flatTensor_fin_iff F)

def pairCoordinates [DecidableEq P] {n : ℕ} (u v : P) (huv : u≠v)
    (r : Fin n ≃ Holant.Certificates.MatchingContractionClosure.Remaining u v) : Fin (n+2) ≃ P where
  toFun := Fin.cases u (Fin.cases v (fun i => (r i).val))
  invFun i := if h : i=u then 0 else if h' : i=v then 1 else (r.symm ⟨i,h,h'⟩).succ.succ
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · change (if h : v=u then (0 : Fin (n+2)) else if h' : v=v then 1 else (r.symm ⟨v,h,h'⟩).succ.succ)=1
        simp [Ne.symm huv]
      · simp [(r k).property.1,(r k).property.2]
  right_inv i := by
    dsimp only
    split_ifs with h h'
    · subst i;rfl
    · subst i;rfl
    · simp

@[simp] theorem pairCoordinates_first [DecidableEq P] {n : ℕ} (u v : P) (huv : u≠v)
    (r : Fin n ≃ Holant.Certificates.MatchingContractionClosure.Remaining u v) : pairCoordinates u v huv r 0=u := rfl
@[simp] theorem pairCoordinates_second [DecidableEq P] {n : ℕ} (u v : P) (huv : u≠v)
    (r : Fin n ≃ Holant.Certificates.MatchingContractionClosure.Remaining u v) : pairCoordinates u v huv r 1=v := rfl
@[simp] theorem pairCoordinates_tail [DecidableEq P] {n : ℕ} (u v : P) (huv : u≠v)
    (r : Fin n ≃ Holant.Certificates.MatchingContractionClosure.Remaining u v) (i : Fin n) : pairCoordinates u v huv r i.succ.succ=(r i).val := rfl

theorem named_contract_coordinates [DecidableEq P] {n : ℕ} (u v : P) (huv : u≠v)
    (r : Fin n ≃ Holant.Certificates.MatchingContractionClosure.Remaining u v) (C : Kernel ℂ) (F : Tensor ℂ P) :
    Tensor.reindex r.symm (Holant.Certificates.MatchingContractionClosure.contractPair u v C F)=
      Signature.contract C (Tensor.reindex (pairCoordinates u v huv r).symm F) := by
  funext x
  have hw (a b : Bool) :
      Holant.Certificates.MatchingContractionClosure.insertPair u v a b (Holant.Certificates.MatchingContractionClosure.extendRemaining u v (fun p => x (r.symm p))) =
      fun p => ((Fin.cons a (Fin.cons b x)) : Fin (n+2) → Bool) ((pairCoordinates u v huv r).symm p) := by
    funext p
    obtain ⟨i,rfl⟩ := (pairCoordinates u v huv r).surjective p
    rw [Equiv.symm_apply_apply]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [pairCoordinates_first,Holant.Certificates.MatchingContractionClosure.insertPair_first huv,Fin.cons_zero]
    · refine Fin.cases ?_ (fun k => ?_) j
      · change Holant.Certificates.MatchingContractionClosure.insertPair u v a b _ v=b
        exact Holant.Certificates.MatchingContractionClosure.insertPair_second _ _ _ _ _
      · rw [pairCoordinates_tail,Holant.Certificates.MatchingContractionClosure.insertPair_other]
        · simp [Holant.Certificates.MatchingContractionClosure.extendRemaining_apply]
        · exact (r k).property.1
        · exact (r k).property.2
  simp only [Tensor.reindex,Holant.Certificates.MatchingContractionClosure.contractPair,Signature.contract,hw]

theorem flatTensorOrZero_contractPair [Fintype P] [DecidableEq P]
    (u v : P) (huv : u≠v) (eta : ZMod 2) (F : Tensor ℂ P)
    (hF : FlatTensorOrZero F) : FlatTensorOrZero (Holant.Certificates.MatchingContractionClosure.contractPair u v (parityKernel eta) F) := by
  let r := (Fintype.equivFin (Holant.Certificates.MatchingContractionClosure.Remaining u v)).symm
  have h := hF.reindex (pairCoordinates u v huv r).symm
  have hs := (flatTensorOrZero_fin_iff _).mp h
  have hc := flatOrZero_contract _ hs eta
  rw [←named_contract_coordinates u v huv r] at hc
  have hc' := (flatTensorOrZero_fin_iff _).mpr hc
  have H := hc'.reindex r
  have he : Tensor.reindex r (Tensor.reindex r.symm (Holant.Certificates.MatchingContractionClosure.contractPair u v (parityKernel eta) F))=
      Holant.Certificates.MatchingContractionClosure.contractPair u v (parityKernel eta) F := by
    funext x
    simp only [Tensor.reindex,Equiv.apply_symm_apply]
  rwa [he] at H

end
end Holant.ReedMuller.FlatNetwork
