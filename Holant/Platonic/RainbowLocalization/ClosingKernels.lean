import Holant.Kernel
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Push

/-! A spanning set supplies actual nonannihilating kernels, rather than a
linear combination treated as a realizable gadget. -/
namespace Holant.Platonic.RainbowLocalization
noncomputable section
open Holant
open scoped BigOperators

/-- The actual bilinear pairing, linear in its selected kernel. -/
def closingFunctional (U : Kernel ℂ) : Kernel ℂ →ₗ[ℂ] ℂ where
  toFun K := Kernel.pair K U
  map_add' K L := by simp [Kernel.pair,add_mul,Finset.sum_add_distrib]
  map_smul' c K := by simp [Kernel.pair,mul_assoc,←Finset.mul_sum]

 theorem exists_actual_closing_kernel (D : Set (Kernel ℂ))
    (hD : Submodule.span ℂ D=⊤) (U : Kernel ℂ) (hU : U≠0) :
    ∃K∈D,Kernel.pair K U≠0 := by
  classical
  by_contra hn
  push_neg at hn
  have hs : Submodule.span ℂ D≤LinearMap.ker (closingFunctional U) :=
    Submodule.span_le.mpr (fun K hK => hn K hK)
  rw [hD] at hs
  obtain ⟨a,ha⟩ := Function.ne_iff.mp hU
  obtain ⟨b,hb⟩ := Function.ne_iff.mp ha
  let K : Kernel ℂ := fun i j=>if i=a ∧ j=b then 1 else 0
  have hz : Kernel.pair K U=0 := hs (show K∈(⊤ : Submodule ℂ (Kernel ℂ)) from trivial)
  apply hb
  cases a <;> cases b <;> simpa [Kernel.pair,K] using hz

/-- One actual kernel is selected for every nonzero common binary factor. -/
 theorem choose_actual_closing_kernels {E : Type*} [Fintype E]
    (D : Set (Kernel ℂ)) (hD : Submodule.span ℂ D=⊤)
    (U : E→Kernel ℂ) (hU : ∀e,U e≠0) :
    ∃C : E→Kernel ℂ,(∀e,C e∈D) ∧ (∀e,Kernel.pair (C e) (U e)≠0) ∧
      (∏e,Kernel.pair (C e) (U e))≠0 := by
  choose C hc hp using fun e=>exists_actual_closing_kernel D hD (U e) (hU e)
  exact ⟨C,hc,hp,Finset.prod_ne_zero_iff.mpr (fun e _=>hp e)⟩

 theorem closing_product_identity {E A : Type*} [Fintype E] [DecidableEq E]
    (C U : E→Kernel ℂ) (q : A→ℂ) (x : A) :
    (∑b : E→Bool×Bool,(∏e,C e (b e).1 (b e).2)*
      (∏e,U e (b e).1 (b e).2)*q x)=
      (∏e,Kernel.pair (C e) (U e))*q x := by
  rw [←Finset.sum_mul]
  congr 1
  simp_rw [←Finset.prod_mul_distrib]
  calc
    _ = ∏e,∑z : Bool×Bool,C e z.1 z.2*U e z.1 z.2 :=
      (Fintype.prod_sum (fun (e : E) (z : Bool×Bool)=>C e z.1 z.2*U e z.1 z.2)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e he
      simp [Kernel.pair,Fintype.sum_prod_type]

/-- The same selected kernels preserve every residual tensor sharing the
common factors; the scalar is exact and nonzero. -/
 theorem simultaneous_common_factor_closure {E A J : Type*} [Fintype E] [DecidableEq E]
    (D : Set (Kernel ℂ)) (hD : Submodule.span ℂ D=⊤)
    (U : E→Kernel ℂ) (hU : ∀e,U e≠0) (q : J→A→ℂ) :
    ∃(C : E→Kernel ℂ) (s : ℂ),(∀e,C e∈D) ∧ s≠0 ∧
      ∀j x,(∑b : E→Bool×Bool,(∏e,C e (b e).1 (b e).2)*
        (∏e,U e (b e).1 (b e).2)*q j x)=s*q j x := by
  obtain ⟨C,hC,hp,hs⟩ := choose_actual_closing_kernels D hD U hU
  exact ⟨C,∏e,Kernel.pair (C e) (U e),hC,hs,fun j x=>closing_product_identity C U (q j) x⟩

end
end Holant.Platonic.RainbowLocalization
