import Holant.Platonic.StabilizerCode.EncoderBridge
import Holant.Platonic.StabilizerShortening.Source

/-! Frobenius reconstruction from the literal two-port card map. The encoder,
its semantic stabilizer property and the nonaffine logical residue are derived
from the actual tetrahedral tests, rather than supplied as hypotheses. -/
namespace Holant.Platonic.TetrahedralLocalization
open Holant Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure Holant.Platonic.StabilizerShortening
open Holant.Certificates.TetrahedralAffine Holant.Certificates.MatchingProductBridge
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The first two physical ports, with their original order retained. -/
def firstPair (n : ℕ) : (Bool ⊕ Fin n) ≃ Fin (n+2) where
  toFun := Sum.elim (fun b => if b then 1 else 0) (fun j => j.succ.succ)
  invFun := Fin.cases (.inl false) (Fin.cases (.inl true) Sum.inr)
  left_inv j := by cases j with
    | inl b => cases b <;> rfl
    | inr j => rfl
  right_inv j := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases <;> rfl

@[simp] theorem pairInsert_firstPair (a b : Bool) (x : Word n) :
    pairInsert (firstPair n) a b x=Fin.cons a (Fin.cons b x) := by
  ext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases <;> rfl

/-- Bilinear contraction, linear in the complete two-by-two coefficient table. -/
def frobeniusMap (f : Signature ℂ (n+2)) : Binary →ₗ[ℂ] Signature ℂ n where
  toFun K := pairCard (firstPair n) K f
  map_add' K L := by ext x;simp [pairCard,add_mul,Finset.sum_add_distrib]
  map_smul' c K := by ext x;simp [pairCard,mul_assoc,mul_add]

/-- Matrix units pick out the four actual Boolean slices without conjugation. -/
theorem frobeniusMap_unit (f : Signature ℂ (n+2)) (a b : Bool) :
    frobeniusMap f (fun c d => if c=a ∧ d=b then 1 else 0)=
      (fun x => f (Fin.cons a (Fin.cons b x))) := by
  ext x
  cases a <;> cases b <;> simp [frobeniusMap,pairCard]

/-- Exact identity-tensor-encoder reconstruction of the original tensor. -/
theorem reconstruct_from_image (f : Signature ℂ (n+2))
    {k : ℕ} (V : StabilizerIsometry k n)
    (Ψ : Binary →ₗ[ℂ] Signature ℂ k) (hΦ : frobeniusMap f=V.map.comp Ψ) :
    tensorMap 2 V.map (tensorMap 2 V.adjoint f)=f := by
  have hs (a b : Bool) :
      V.map (V.adjoint (fun x => f (Fin.cons a (Fin.cons b x))))=
        (fun x => f (Fin.cons a (Fin.cons b x))) := by
    have he := LinearMap.congr_fun hΦ (fun c d => if c=a ∧ d=b then 1 else 0)
    rw [frobeniusMap_unit] at he
    rw [he]
    simp
  apply columns_ext
  intro a
  simp only [tensorMap_succ,tensorMap_zero,column_prependMap]
  apply columns_ext
  intro b
  simp only [column_prependMap]
  have hc : column 0 b (column 0 a f)=(fun x => f (Fin.cons a (Fin.cons b x))) := by
    ext x
    simp only [column_zero_apply]
  exact (congrArg (fun v => V.map (V.adjoint v)) hc).trans ((hs a b).trans hc.symm)

/-- The common code construction yields a genuine source-primary stabilizer
isometry and a nonaffine residue, with no normalization or encoder premise. -/
theorem source_frobenius_reconstruction (f : Signature ℂ (n+2))
    (hf : ¬ComplexAffine f)
    (htest : ∀K,tetrahedralBase K → frobeniusMap f K=0 ∨ ComplexAffine (frobeniusMap f K)) :
    ∃k : ℕ,k≤4 ∧ ∃V : StabilizerIsometry k n,
      IsStabilizerIsometry V.map ∧ ∃xi : Signature ℂ (k+2),
        ¬ComplexAffine xi ∧ tensorMap 2 V.map xi=f := by
  obtain ⟨k,hk,V,Ψ,hΦ,_,_⟩ := source_encoded_four_active_qubits (frobeniusMap f) htest
  let xi := tensorMap 2 V.adjoint f
  have he : tensorMap 2 V.map xi=f := reconstruct_from_image f V Ψ hΦ
  refine ⟨k,hk,V,V.semantic,xi,?_,he⟩
  intro ha
  apply hf
  rw [←he]
  exact (semantic_isometry_affine_iff _ (tensorMap_stabilizer 2 V.map V.semantic) xi).mpr ha

end
end Holant.Platonic.TetrahedralLocalization
