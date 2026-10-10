import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesAlgebra
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesNorm

/-! After equalizing the diagonal, at most one positive square and one
pin0 row/column cap supplies an infinite binary ratio, unless an actual
scalar equality power is already forced. No four-port interpolation occurs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesChoice
open Holant
namespace A
export GlobalCloseCompletionPairedSeriesAlgebra (square00 square11)
end A
namespace C
export GlobalCloseCompletionPairedSeriesNorm (Infinite square_cap_infinite twice_infinite)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]
def Infinite (z : K) : Prop := ∀n : ℕ,0<n→z^n≠1

theorem infinite_map (phi : K→+*ℂ) (z : K) : Infinite z ↔ C.Infinite (phi z) := by
  constructor
  · intro h n hn he
    exact h n hn (phi.injective (by simpa only [map_pow,map_one] using he))
  · intro h n hn he
    exact h n hn (by simpa only [map_pow,map_one] using congrArg phi he)

theorem square01 (B : Matrix Bool Bool K) : (B^2) false true=B false true*(B false false+B true true) := by
  simp [pow_two,Matrix.mul_apply]
  ring

def Read (B : Matrix Bool Bool K) (k : ℕ) (swap : Bool) : Matrix Bool Bool K :=
  if swap then (B^k).transpose else B^k

def Cap (B : Matrix Bool Bool K) : Prop := ∃k : ℕ,0<k ∧ ∃swap : Bool,
  (Read B k swap) false false≠0 ∧ (Read B k swap) false true≠0 ∧
    Infinite ((Read B k swap) false true/(Read B k swap) false false)

variable (phi : K→+*ℂ) (B : Matrix Bool Bool K)
variable (nonzero : B false false≠0) (same : B true true=B false false) (det : B.det≠0)

include phi nonzero same det in
theorem upper (upper : B false true≠0) :
    ((B^2) false false=0 ∧ (B^2) true true=0) ∨ Cap B := by
  classical
  let p:=B false true/B false false
  let q:=B true false/B false false
  by_cases hp : Infinite p
  · exact Or.inr ⟨1,by decide,false,by simpa [Read],by simpa [Read] using upper,by simpa [Read] using hp⟩
  by_cases hq : Infinite q ∧ B true false≠0
  · exact Or.inr ⟨1,by decide,true,by simpa [Read],by simpa [Read] using hq.2,by simpa [Read] using hq.1⟩
  by_cases hdiag : (B^2) false false=0
  · exact Or.inl ⟨hdiag,by simpa only [A.square00,A.square11,same] using hdiag⟩
  right
  refine ⟨2,by decide,false,by simpa [Read] using hdiag,?_,?_⟩
  · change (B^2) false true≠0
    rw [square01,same,←two_mul]
    exact mul_ne_zero upper (mul_ne_zero (show (2 : K)≠0 by norm_num) nonzero)
  · change Infinite ((B^2) false true/(B^2) false false)
    have ratio : (B^2) false true/(B^2) false false=2*p/(1+p*q) := by
      rw [square01,A.square00,same]
      dsimp [p,q]
      field_simp
      <;> ring
    rw [ratio]
    apply (infinite_map phi _).mpr
    have mapped : phi (2*p/(1+p*q))=2*phi p/(1+phi p*phi q) := by
      have two : phi (2 : K) = (2 : ℂ) := by
        rw [show (2 : K)=1+1 by ring,map_add,map_one]
        ring
      simp [two]
    rw [mapped]
    by_cases zero : B true false=0
    · have qzero : q=0 := by simp [q,zero]
      simp only [qzero,map_zero,mul_zero,add_zero,div_one]
      exact C.twice_infinite (phi p) (fun h=>hp ((infinite_map phi p).mpr h))
    · have fq : ¬Infinite q := fun h=>hq ⟨h,zero⟩
      have pq : p*q≠1 := by
        intro he
        have hb : B false true*B true false=B false false^2 := by
          dsimp [p,q] at he
          field_simp at he
          linear_combination he
        apply det
        rw [Holant.Complexity.BinaryInterpolation.det_entries,same,hb]
        ring
      have den : 1+p*q≠0 := by
        intro he
        apply hdiag
        rw [A.square00]
        have he' : B false false^2+B false true*B true false=0 := by
          dsimp [p,q] at he
          field_simp at he
          linear_combination he
        exact he'
      apply C.square_cap_infinite (phi p) (phi q)
        (fun h=>hp ((infinite_map phi p).mpr h)) (fun h=>fq ((infinite_map phi q).mpr h))
      · intro he
        apply pq
        apply phi.injective
        simpa only [map_mul,map_one] using he
      · intro he
        apply den
        apply phi.injective
        simpa only [map_add,map_one,map_mul,map_zero] using he

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesChoice
end
