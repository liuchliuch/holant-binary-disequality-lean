import Holant.Certificates.FourthRootOdd.DenseData
import Holant.Tractable.Scalars

/-! Soundness of the finite dense-output certificates in the source's literal
ρ r^weight (-1)^(s dot x) even-support formula. The square root is the explicitly
algebraic eighth-root constant, not an assumed complex parameter. -/
noncomputable section
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops Holant.Tractable

def signExponent (s x : Fin 4 → Bool) : ℕ := ∑ j, if s j && x j then 1 else 0
def denseFormula (ρ r : ℂ) (s : Fin 4 → Bool) : Signature ℂ 4 := fun x =>
  if evenWord x then ρ*r^wordWeight x*(-1)^signExponent s x else 0
def DenseProduct (f : Signature ℂ 4) : Prop :=
  ∃ ρ r : ℂ, ρ≠0 ∧ r≠0 ∧ ∃ s : Fin 4 → Bool, f=denseFormula ρ r s

def eighthRoot (u : Fin 4) : ℂ := (zetaEight : ℂ)^u.val

theorem embed_fourthRoot (u : Fin 4) : embed (fourthRoot u)=Complex.I^u.val := by
  fin_cases u <;> norm_num [fourthRoot,embed,pow_succ]

theorem eighthRoot_sq (u : Fin 4) : eighthRoot u^2=embed (fourthRoot u) := by
  have hz : (zetaEight : ℂ)^2=Complex.I := by
    change ((zetaEight^2 : AlgebraicComplex) : ℂ)=(imaginaryUnit : ℂ)
    exact congrArg (fun z : AlgebraicComplex => (z : ℂ)) zetaEight_sq
  rw [eighthRoot,←pow_mul,Nat.mul_comm u.val 2,pow_mul,hz,embed_fourthRoot]

theorem eighthRoot_ne_zero (u : Fin 4) : eighthRoot u≠0 := by
  apply pow_ne_zero
  exact_mod_cast zetaEight_ne_zero

theorem embed_gpow (z : Gaussian) (n : ℕ) : embed (gpow z n)=embed z^n := by
  induction n with
  | zero => simp [gpow,embed]
  | succ n ih => rw [gpow,embed_mul,ih,pow_succ]

theorem four_sign_power (a b c d : Bool) :
    (-1 : ℂ)^((if a then 1 else 0)+(if b then 1 else 0)+(if c then 1 else 0)+(if d then 1 else 0)) =
      if a ^^ b ^^ c ^^ d then -1 else 1 := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num

theorem signExponent_power (m : Fin 16) (x : Fin 4 → Bool) :
    (-1 : ℂ)^signExponent (maskBit m) x=if maskSign m x then -1 else 1 := by
  have hs : signExponent (maskBit m) x=
      (if maskBit m 0 && x 0 then 1 else 0)+(if maskBit m 1 && x 1 then 1 else 0)+
      (if maskBit m 2 && x 2 then 1 else 0)+(if maskBit m 3 && x 3 then 1 else 0) := by
    simp only [signExponent,Fin.sum_univ_succ,Fin.sum_univ_zero]
    simp only [show (Fin.succ 0 : Fin 4)=1 from rfl,
      show (Fin.succ 0).succ = (2 : Fin 4) from rfl,
      show (Fin.succ 0).succ.succ = (3 : Fin 4) from rfl]
    omega
  rw [hs]
  exact four_sign_power (maskBit m 0 && x 0) (maskBit m 1 && x 1)
    (maskBit m 2 && x 2) (maskBit m 3 && x 3)

theorem evenWord_weight : ∀ x : Fin 4 → Bool, evenWord x=true ↔ wordWeight x%2=0 := by decide

theorem embed_denseTable (ρ : Gaussian) (u : Fin 4) (m : Fin 16) (x : Fin 4 → Bool) :
    embed (denseTable ρ u m x)=denseFormula (embed ρ) (eighthRoot u) (maskBit m) x := by
  by_cases hx : evenWord x=true
  · have hw : wordWeight x=2*(wordWeight x/2) := by
      have he := (evenWord_weight x).mp hx
      omega
    have hp : eighthRoot u^wordWeight x=embed (fourthRoot u)^(wordWeight x/2) := by
      conv_lhs => rw [hw]
      rw [pow_mul,eighthRoot_sq]
    simp only [denseTable,denseFormula,hx,↓reduceIte,embed_mul,embed_gpow,hp,signExponent_power]
    cases hs : maskSign m x <;> simp [hs,embed,mul_assoc]
  · simp [denseTable,denseFormula,hx,embed]

theorem dense_output_of_certificate (p : FamilyParameters) (e : Fin 3) (u : Fin 4) (m : Fin 16)
    (h : ValidFamilyWitness p (.inr (e,u,m))) :
    DenseProduct (twoCopyNative (complexOdd (familyState p)) (initialPair e)) := by
  obtain ⟨hρ,hh⟩ := h
  refine ⟨embed (exactTwoCopy (familyState p) (initialPair e) (fun _ => false)),eighthRoot u,
    (not_congr (embed_zero_iff _)).mpr hρ,eighthRoot_ne_zero u,maskBit m,?_⟩
  funext x
  rw [twoCopyNative_eq,←embed_exactTwoCopy,hh,embed_denseTable]

end Holant.Certificates.FourthRootOdd
