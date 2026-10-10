import Holant.Proofs.Hardness.EOBinaryPlaneClassification
import Mathlib.Tactic.LinearCombination

/-! Three literal unary-weight multiplicities suffice for a full hard binary.
The affine/product tests are the actual signature classes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSparseWeightBinary
open Holant Holant.Tractable
open EOBinaryPlaneClassification
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def row (a b c d : AlgebraicComplex) : Signature AlgebraicComplex 2 :=
  fun z => if z 0 then (if z 1 then b else c) else (if z 1 then d else a)
def binary (a b c d u v : AlgebraicComplex) (e : ℕ) : Signature AlgebraicComplex 2 :=
  row (a*u^e) (b*u^e) (c*v^e) (d*v^e)

theorem row_full {a b c d : AlgebraicComplex} (ha : a≠0) (hb : b≠0)
    (hc : c≠0) (hd : d≠0) : Full (row a b c d) := by
  intro z
  cases h0 : z 0 <;> cases h1 : z 1 <;> simp [row,h0,h1,ha,hb,hc,hd]

theorem full {a b c d u v : AlgebraicComplex} (ha : a≠0) (hb : b≠0)
    (hc : c≠0) (hd : d≠0) (hu : u≠0) (hv : v≠0) (e : ℕ) :
    Full (binary a b c d u v e) :=
  row_full (mul_ne_zero ha (pow_ne_zero _ hu)) (mul_ne_zero hb (pow_ne_zero _ hu))
    (mul_ne_zero hc (pow_ne_zero _ hv)) (mul_ne_zero hd (pow_ne_zero _ hv))

private theorem affine_step {a b c d u v : AlgebraicComplex}
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) (hu : u≠0) (hv : v≠0)
    (hne : u^4≠v^4) (hA : Affine (row a b c d)) :
    ¬Affine (row (a*u) (b*u) (c*v) (d*v)) ∧
      ¬Product (row (a*u) (b*u) (c*v) (d*v)) := by
  have hf := row_full ha hb hc hd
  have hg := row_full (mul_ne_zero ha hu) (mul_ne_zero hb hu) (mul_ne_zero hc hv) (mul_ne_zero hd hv)
  have h0 := hA.fourth_power_eq (![false,true] : Fin 2→Bool) ![false,false]
    (hf _) (hf _)
  simp [row] at h0
  constructor
  · intro hB
    have h1 := hB.fourth_power_eq (![false,true] : Fin 2→Bool) ![false,false]
      (hg _) (hg _)
    simp [row] at h1
    have hz : a^4*(u^4-v^4)=0 := by linear_combination -h1 + v^4*h0
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ha)))
  · intro hP
    have hp := (full_product_iff _ hg).mp hP
    have hs := affine_signed_cross _ hf hA
    have hs2 : (a*b)^2=(d*c)^2 := by
      rcases hs with hs | hs
      · change a*b=d*c at hs
        exact congrArg (fun t : AlgebraicComplex => t^2) hs
      · change a*b=-(d*c) at hs
        rw [hs]
        ring
    have hp2 := congrArg (fun t : AlgebraicComplex => t^2) hp
    simp [Cross,row] at hp2
    have hz : (a*b)^2*(u^4-v^4)=0 := by linear_combination hp2 - v^4*hs2
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (mul_ne_zero ha hb))))

private theorem product_step {a b c d u v : AlgebraicComplex}
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) (hu : u≠0) (hv : v≠0)
    (hne : u^4≠v^4) (hP : Product (row a b c d)) :
    ¬Product (row (a*u) (b*u) (c*v) (d*v)) := by
  intro hQ
  have h0 := (full_product_iff _ (row_full ha hb hc hd)).mp hP
  have h1 := (full_product_iff _ (row_full (mul_ne_zero ha hu) (mul_ne_zero hb hu)
    (mul_ne_zero hc hv) (mul_ne_zero hd hv))).mp hQ
  simp [Cross,row] at h0 h1
  have hz : (a*b)*(u^2-v^2)=0 := by linear_combination h1 - v^2*h0
  have h2 : u^2=v^2 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero ha hb))
  apply hne
  calc
    u^4=(u^2)^2 := by ring
    _=(v^2)^2 := congrArg (fun t : AlgebraicComplex=>t^2) h2
    _=v^4 := by ring

theorem exists_hard_binary {a b c d u v : AlgebraicComplex}
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) (hu : u≠0) (hv : v≠0)
    (hne : u^4≠v^4) : ∃e : ℕ,e≤2 ∧ Full (binary a b c d u v e) ∧
      ¬Affine (binary a b c d u v e) ∧ ¬Product (binary a b c d u v e) := by
  by_cases hA : Affine (row a b c d)
  · have h := affine_step ha hb hc hd hu hv hne hA
    exact ⟨1,by omega,full ha hb hc hd hu hv 1,by simpa [binary] using h.1,
      by simpa [binary] using h.2⟩
  · by_cases hP : Product (row a b c d)
    · have hnP := product_step ha hb hc hd hu hv hne hP
      by_cases hB : Affine (row (a*u) (b*u) (c*v) (d*v))
      · have h := affine_step (mul_ne_zero ha hu) (mul_ne_zero hb hu)
          (mul_ne_zero hc hv) (mul_ne_zero hd hv) hu hv hne hB
        exact ⟨2,by omega,full ha hb hc hd hu hv 2,
          by simpa only [binary,pow_two,mul_assoc] using h.1,
          by simpa only [binary,pow_two,mul_assoc] using h.2⟩
      · exact ⟨1,by omega,full ha hb hc hd hu hv 1,by simpa [binary] using hB,
          by simpa [binary] using hnP⟩
    · exact ⟨0,by omega,full ha hb hc hd hu hv 0,by simpa [binary] using hA,
        by simpa [binary] using hP⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSparseWeightBinary
