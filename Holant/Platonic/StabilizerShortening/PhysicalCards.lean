import Holant.Platonic.StabilizerShortening.AffineTools
import Holant.Platonic.StabilizerErasure.BasisColumns
import Holant.Certificates.TetrahedralAffine.Binaries
import Holant.Pauli.ExoticKlein.FiberFactor

/-! Actual two-port cards and genuine positive-arity tensor factors on the
original physical port set. Pair order and the scalar of K are retained. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure
open Holant.Certificates.TetrahedralAffine Holant.Certificates.MatchingProductBridge
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {l m n : ℕ}

def pairInsert (p : (Bool ⊕ Fin n) ≃ Fin m) (a b : Bool) (x : Word n) : Word m :=
  fun j=>Sum.elim (fun c=>if c then b else a) x (p.symm j)

@[simp] theorem pairInsert_first (p : (Bool ⊕ Fin n) ≃ Fin m)
    (a b : Bool) (x : Word n) : pairInsert p a b x (p (.inl false))=a := by simp [pairInsert]
@[simp] theorem pairInsert_second (p : (Bool ⊕ Fin n) ≃ Fin m)
    (a b : Bool) (x : Word n) : pairInsert p a b x (p (.inl true))=b := by simp [pairInsert]
@[simp] theorem pairInsert_remaining (p : (Bool ⊕ Fin n) ≃ Fin m)
    (a b : Bool) (x : Word n) (i : Fin n) : pairInsert p a b x (p (.inr i))=x i := by simp [pairInsert]

theorem pairInsert_eta (p : (Bool ⊕ Fin n) ≃ Fin m) (w : Word m) :
    pairInsert p (w (p (.inl false))) (w (p (.inl true))) (fun j=>w (p (.inr j)))=w := by
  ext j
  obtain ⟨j,rfl⟩ := p.surjective j
  cases j with
  | inl b => cases b <;> simp
  | inr j => simp

def pairCard (p : (Bool ⊕ Fin n) ≃ Fin m) (K : Kernel ℂ) :
    Signature ℂ m →ₗ[ℂ] Signature ℂ n where
  toFun f x := ∑a : Bool,∑b : Bool,K a b*f (pairInsert p a b x)
  map_add' f g := by ext x;simp [mul_add,Finset.sum_add_distrib]
  map_smul' c f := by ext x;simp [Finset.mul_sum,mul_left_comm,mul_add]

/-- An actual fixed tetrahedral representative, contracted on two different
original physical ports, with the actual nonzero nonaffine residual tensor. -/
def HasNonaffineTetrahedralCard (f : Signature ℂ m) : Prop :=
  ∃n : ℕ,∃p : (Bool ⊕ Fin n) ≃ Fin m,∃r : Representative,
    pairCard p (complexKernel r) f≠0 ∧ ¬ComplexAffine (pairCard p (complexKernel r) f)

theorem pairInsert_eq_iff (p : (Bool ⊕ Fin n) ≃ Fin m)
    (a b : Bool) (x : Word n) (z : Word m) :
    pairInsert p a b x=z ↔
      a=z (p (.inl false)) ∧ b=z (p (.inl true)) ∧ x=(fun j=>z (p (.inr j))) := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h (p (.inl false)),
      by simpa using congrFun h (p (.inl true)),
      funext (fun j=>by simpa using congrFun h (p (.inr j)))⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact pairInsert_eta p z

theorem pairCard_ket (p : (Bool ⊕ Fin n) ≃ Fin m) (K : Kernel ℂ) (z : Word m) :
    pairCard p K (ket z)=K (z (p (.inl false))) (z (p (.inl true))) •
      ket (fun j=>z (p (.inr j))) := by
  ext x
  cases h0 : z (p (.inl false)) <;> cases h1 : z (p (.inl true)) <;>
    simp [pairCard,ket,pairInsert_eq_iff,mul_ite,h0,h1]

/-- Recovery through an affine Boolean sampling map and a nowhere-zero
quadratic multiplier reflects nonaffinity and also proves nonvanishing. -/
theorem nonaffine_of_affine_recovery (f : Signature ℂ l) (g : Signature ℂ n)
    (a : Signature ℂ l) (p : Word l → Word n) (hp : IsAffineMap p)
    (ha : ∀x,a x≠0) (hai : ComplexAffine (fun x=>(a x)⁻¹))
    (he : ∀x,g (p x)=a x*f x) (hf : ¬ComplexAffine f) :
    g≠0 ∧ ¬ComplexAffine g := by
  have hn : ¬ComplexAffine g := by
    intro hg
    have hh := affine_complex_mul hai (affine_complex_precompose hg p hp)
    have he' : (fun x=>(a x)⁻¹*g (p x))=f := by
      ext x
      rw [he,←mul_assoc,inv_mul_cancel₀ (ha x),one_mul]
    rw [he'] at hh
    exact hf hh
  exact ⟨fun hz=>hn (hz ▸ affine_zero_complex),hn⟩

def unaryPorts (r : Fin (n+1)) : (Fin 1 ⊕ Fin n) ≃ Fin (n+1) where
  toFun := Sum.elim (fun _=>r) r.succAbove
  invFun j := if h : j=r then .inl 0 else .inr ((finSuccAboveEquiv r).symm ⟨j,h⟩)
  left_inv j := by
    cases j with
    | inl i => fin_cases i;simp
    | inr i => simp [Fin.succAbove_ne,←finSuccAboveEquiv_apply]
  right_inv j := by
    dsimp only
    split_ifs with h
    · exact h.symm
    · exact congrArg Subtype.val ((finSuccAboveEquiv r).apply_symm_apply ⟨j,h⟩)

theorem proper_factor_of_unary_separation (f : Signature ℂ (n+1))
    (r : Fin (n+1)) (u : Bool → ℂ) (g : Signature ℂ n)
    (hn : 0<n) (hf : f≠0)
    (he : ∀w,f w=u (w r)*g (r.removeNth w)) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor f := by
  apply Holant.Pauli.ExoticKlein.Fiber.factor_of_split (unaryPorts r)
    (fun x : Word 1=>u (x 0)) g f (by norm_num) (by simpa using hn) hf
  ext w
  exact he w

end
end Holant.Platonic.StabilizerShortening
