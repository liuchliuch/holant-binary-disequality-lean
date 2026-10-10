import Holant.Platonic.StabilizerShortening.PhysicalCards
import Holant.Platonic.StabilizerShortening.TensorExtension

/-! Adding untouched physical ports retains the same actual selected pair
and the same genuine unary factor; all port bijections are explicit. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure
open Holant.Certificates.TetrahedralAffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k m n : ℕ}

def prependSplitPorts {A : Type*} (p : (A ⊕ Fin n) ≃ Fin m) :
    (A ⊕ Fin (n+1)) ≃ Fin (m+1) where
  toFun := Sum.elim (fun a=>(p (.inl a)).succ)
    (Fin.cases 0 (fun j=>(p (.inr j)).succ))
  invFun := Fin.cases (.inr 0) (fun j=>Sum.map id Fin.succ (p.symm j))
  left_inv j := by
    cases j with
    | inl a => simp
    | inr j => cases j using Fin.cases <;> simp
  right_inv j := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      obtain ⟨j,rfl⟩ := p.surjective j
      cases j <;> simp

@[simp] theorem prependSplitPorts_left {A : Type*} (p : (A ⊕ Fin n) ≃ Fin m) (a : A) :
    prependSplitPorts p (.inl a)=(p (.inl a)).succ := rfl
@[simp] theorem prependSplitPorts_zero {A : Type*} (p : (A ⊕ Fin n) ≃ Fin m) :
    prependSplitPorts p (.inr 0)=0 := rfl
@[simp] theorem prependSplitPorts_succ {A : Type*} (p : (A ⊕ Fin n) ≃ Fin m) (j : Fin n) :
    prependSplitPorts p (.inr j.succ)=(p (.inr j)).succ := rfl

def tensorSplitPorts {A : Type*} (t : ℕ) (p : (A ⊕ Fin n) ≃ Fin m) :
    (A ⊕ Fin (n+t)) ≃ Fin (m+t) :=
  match t with
  | 0 => p
  | t+1 => prependSplitPorts (tensorSplitPorts t p)

theorem pairInsert_prepend (p : (Bool ⊕ Fin n) ≃ Fin m)
    (a b : Bool) (x : Word (n+1)) :
    pairInsert (prependSplitPorts p) a b x=
      Fin.cons (x 0) (pairInsert p a b (Fin.tail x)) := by
  ext j
  obtain ⟨j,rfl⟩ := (prependSplitPorts p).surjective j
  cases j with
  | inl c => cases c <;> simp [pairInsert,prependSplitPorts,Fin.tail]
  | inr j => cases j using Fin.cases <;> simp [pairInsert,prependSplitPorts,Fin.tail]

theorem pairCard_prepend (p : (Bool ⊕ Fin n) ≃ Fin m) (K : Kernel ℂ) :
    pairCard (prependSplitPorts p) K=prependMap (pairCard p K) := by
  ext f x
  simp [pairCard,prependMap,pairInsert_prepend,column,Fin.insertNth_zero]

theorem tensorMap_pairCard (t : ℕ) (p : (Bool ⊕ Fin n) ≃ Fin m) (K : Kernel ℂ) :
    tensorMap t (pairCard p K)=pairCard (tensorSplitPorts t p) K := by
  induction t with
  | zero => rfl
  | succ t ih => rw [tensorMap_succ,ih,←pairCard_prepend];rfl

theorem actual_card_of_tensorMap (t : ℕ) (p : (Bool ⊕ Fin n) ≃ Fin m)
    (r : Representative) (f : Signature ℂ (m+t))
    (h : tensorMap t (pairCard p (complexKernel r)) f≠0 ∧
      ¬ComplexAffine (tensorMap t (pairCard p (complexKernel r)) f)) :
    HasNonaffineTetrahedralCard f := by
  exact ⟨n+t,tensorSplitPorts t p,r,by simpa only [tensorMap_pairCard] using h⟩

def unaryFactorMap (p : (Fin 1 ⊕ Fin n) ≃ Fin m) (u : Signature ℂ 1)
    (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n) : Signature ℂ k →ₗ[ℂ] Signature ℂ m where
  toFun f x := u (fun j=>x (p (.inl j)))*W f (fun j=>x (p (.inr j)))
  map_add' f g := by ext x;simp [mul_add]
  map_smul' c f := by ext x;simp [mul_left_comm]

theorem unaryFactorMap_prepend (p : (Fin 1 ⊕ Fin n) ≃ Fin m) (u : Signature ℂ 1)
    (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    prependMap (unaryFactorMap p u W)=
      unaryFactorMap (prependSplitPorts p) u (prependMap W) := by
  ext f x
  simp only [prependMap,unaryFactorMap,LinearMap.coe_mk,AddHom.coe_mk,
    prependSplitPorts_left,Fin.tail]
  congr 1

theorem unaryFactorMap_tensorMap (t : ℕ) (p : (Fin 1 ⊕ Fin n) ≃ Fin m)
    (u : Signature ℂ 1) (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    tensorMap t (unaryFactorMap p u W)=
      unaryFactorMap (tensorSplitPorts t p) u (tensorMap t W) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [tensorMap_succ,ih,unaryFactorMap_prepend];rfl

theorem unaryFactorMap_proper (p : (Fin 1 ⊕ Fin n) ≃ Fin m) (u : Signature ℂ 1)
    (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (f : Signature ℂ k)
    (hn : 0<n) (hf : unaryFactorMap p u W f≠0) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (unaryFactorMap p u W f) := by
  exact Holant.Pauli.ExoticKlein.Fiber.factor_of_split p u (W f) _
    (by norm_num) (by simpa using hn) hf rfl

end
end Holant.Platonic.StabilizerShortening
