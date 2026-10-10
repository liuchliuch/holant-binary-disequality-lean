import Holant.Platonic.TetrahedralEightPortBase.NoUnary

/-! Exact restriction and contraction identities for genuine factors of a
physical tensor. All contractions use the original fixed tetrahedral kernels. -/
namespace Holant.Platonic.TetrahedralEightPortBase
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralEightPort.SafeAffine
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open Holant.Platonic.TetrahedralLocalization Holant.Platonic.ActiveSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {l m n d : ℕ}

def splitWord (p : (Fin m ⊕ Fin n) ≃ Fin l) (x : Word m) (y : Word n) : Word l :=
  fun j=>Sum.elim x y (p.symm j)

@[simp] theorem splitWord_left (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (x : Word m) (y : Word n) (j : Fin m) : splitWord p x y (p (.inl j))=x j := by
  simp [splitWord]
@[simp] theorem splitWord_right (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (x : Word m) (y : Word n) (j : Fin n) : splitWord p x y (p (.inr j))=y j := by
  simp [splitWord]

theorem splitWord_affine_left (p : (Fin m ⊕ Fin n) ≃ Fin l) (y : Word n) :
    IsAffineMap (fun x=>splitWord p x y) := by
  intro x z
  funext j
  cases h : p.symm j with
  | inl i => simp [splitWord,h,AffinePhase.xor,origin]
  | inr i => cases hy : y i <;> simp [splitWord,h,AffinePhase.xor,hy]

theorem splitWord_affine_right (p : (Fin m ⊕ Fin n) ≃ Fin l) (x : Word m) :
    IsAffineMap (fun y=>splitWord p x y) := by
  intro y z
  funext j
  cases h : p.symm j with
  | inl i => cases hx : x i <;> simp [splitWord,h,AffinePhase.xor,hx]
  | inr i => simp [splitWord,h,AffinePhase.xor,origin]

theorem affine_factor_left (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (f : Signature ℂ m) (g : Signature ℂ n) (hg : g≠0)
    (h : ComplexAffine (Tensor.reindex p (Tensor.tensor f g))) : ComplexAffine f := by
  obtain ⟨y,hy⟩ := Function.ne_iff.mp hg
  have hh := affine_complex_precompose h _ (splitWord_affine_left p y)
  have he : (fun x=>Tensor.reindex p (Tensor.tensor f g) (splitWord p x y))=
      (fun x=>g y*f x) := by
    funext x
    simp [Tensor.reindex,Tensor.tensor,mul_comm]
  rw [he] at hh
  exact (affine_complex_scale_iff (g y) hy f).mp hh

theorem affine_factor_right (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (f : Signature ℂ m) (g : Signature ℂ n) (hf : f≠0)
    (h : ComplexAffine (Tensor.reindex p (Tensor.tensor f g))) : ComplexAffine g := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hf
  have hh := affine_complex_precompose h _ (splitWord_affine_right p x)
  have he : (fun y=>Tensor.reindex p (Tensor.tensor f g) (splitWord p x y))=
      (fun y=>f x*g y) := by
    funext y
    simp [Tensor.reindex,Tensor.tensor]
  rw [he] at hh
  exact (affine_complex_scale_iff (f x) hx g).mp hh

theorem affine_tensor (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (f : Signature ℂ m) (g : Signature ℂ n)
    (hf : ComplexAffine f) (hg : ComplexAffine g) :
    ComplexAffine (Tensor.reindex p (Tensor.tensor f g)) := by
  exact affine_complex_mul
    (affine_complex_precompose hf _ (coordinates_isAffineMap (fun j=>p (.inl j))))
    (affine_complex_precompose hg _ (coordinates_isAffineMap (fun j=>p (.inr j))))

theorem tensor_ne_zero (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (f : Signature ℂ m) (g : Signature ℂ n) (hf : f≠0) (hg : g≠0) :
    Tensor.reindex p (Tensor.tensor f g)≠0 := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hf
  obtain ⟨y,hy⟩ := Function.ne_iff.mp hg
  intro hz
  have h := congrFun hz (splitWord p x y)
  simp only [Tensor.reindex,Tensor.tensor,splitWord_left,splitWord_right,Pi.zero_apply] at h
  exact mul_ne_zero hx hy h

/-- Contract the first two coordinates of the left factor, keeping its
remaining coordinates and the untouched right factor in an arbitrary order. -/
def factorPair (p : (Fin (m+2) ⊕ Fin n) ≃ Fin l)
    (r : (Fin m ⊕ Fin n) ≃ Fin d) : (Bool ⊕ Fin d) ≃ Fin l :=
  (Equiv.sumCongr (Equiv.refl Bool) r.symm).trans
    ((Equiv.sumAssoc Bool (Fin m) (Fin n)).symm.trans
      ((Equiv.sumCongr (firstPair m) (Equiv.refl (Fin n))).trans p))

theorem pairCard_factor (p : (Fin (m+2) ⊕ Fin n) ≃ Fin l)
    (r : (Fin m ⊕ Fin n) ≃ Fin d) (K : Kernel ℂ)
    (f : Signature ℂ (m+2)) (g : Signature ℂ n) :
    pairCard (factorPair p r) K (Tensor.reindex p (Tensor.tensor f g))=
      Tensor.reindex r (Tensor.tensor (frobeniusMap f K) g) := by
  funext x
  have hl (a b : Bool) :
      (fun j=>pairInsert (factorPair p r) a b x (p (.inl j)))=
        Fin.cons a (Fin.cons b (fun j=>x (r (.inl j)))) := by
    funext j
    cases j using Fin.cases with
    | zero => simp [pairInsert,factorPair,firstPair]
    | succ j => cases j using Fin.cases with
      | zero =>
        change pairInsert (factorPair p r) a b x ((factorPair p r) (.inl true))=b
        exact pairInsert_second _ _ _ _
      | succ j => simp [pairInsert,factorPair,firstPair]
  have hr (a b : Bool) :
      (fun j=>pairInsert (factorPair p r) a b x (p (.inr j)))=
        (fun j=>x (r (.inr j))) := by
    funext j
    simp [pairInsert,factorPair]
  simp only [pairCard,LinearMap.coe_mk,AddHom.coe_mk,Tensor.reindex,Tensor.tensor,hl,hr,
    frobeniusMap,pairInsert_firstPair,Fintype.sum_bool]
  ring

theorem nonzero_internal_card (f : Signature ℂ (m+2)) (hf : f≠0) :
    ∃ K : Kernel ℂ, groupDirection .tetrahedral K ∧ frobeniusMap f K≠0 := by
  have hΦ : frobeniusMap f≠0 := by
    intro hz
    apply hf
    funext w
    have h := LinearMap.congr_fun hz
      (fun c d=>if c=w 0 ∧ d=w 1 then (1:ℂ) else 0)
    rw [frobeniusMap_unit] at h
    have hh := congrFun h (fun j=>w j.succ.succ)
    have he : Fin.cons (w 0) (Fin.cons (w 1) (fun j=>w j.succ.succ))=w := by
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j => cases j using Fin.cases <;> rfl
    simpa only [LinearMap.zero_apply,Pi.zero_apply,he] using hh
  obtain ⟨K,hK,hKn⟩ := exists_nonzero_tetrahedral (frobeniusMap f) hΦ
  exact ⟨K,⟨1,one_ne_zero,K,hK,by simp⟩,hKn⟩

end
end Holant.Platonic.TetrahedralEightPortBase
