import Holant.Dihedral.CompatibleCoefficientLine.Closure

/-! A coefficient discrepancy in two actual inherited cards forces a literal
nonzero minor of the p|e flattening of their common physical quaternary. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

/-- On a common parity plane, projective inequality is exactly the source
ordered two-entry determinant test. -/
theorem factorDet_zero_iff {α : Bool} {A B : Mat} (hA : HasParity α A) (hB : HasParity α B) :
    factorDet α A B = 0 ↔ ProjectivelyEqual B A := by
  constructor
  · intro hd
    obtain ⟨w,hw,rfl⟩ := hA
    obtain ⟨v,hv,rfl⟩ := hB
    have hh : w false*v true-w true*v false=0 := by
      cases α <;> simpa [factorDet,monomial] using hd
    refine ⟨v false / w false,div_ne_zero (hv false) (hw false),?_⟩
    funext a b
    cases α <;> cases a <;> cases b <;>
      simp [monomial,Marked.scale] <;> field_simp [hw false] <;>
      linear_combination hh
  · rintro ⟨c,hc,rfl⟩
    simp only [factorDet,Marked.scale]
    ring

/-- The two protected columns in the literal p|e flattening. -/
def flattenEntry (q : Signature Scalar 4) (p e : Bool × Bool) : Scalar :=
  q (pair p.1 p.2 ![e.1,e.2])

def minor (q : Signature Scalar 4) (p₀ p₁ e₀ e₁ : Bool × Bool) : Scalar :=
  flattenEntry q p₀ e₀ * flattenEntry q p₁ e₁ -
    flattenEntry q p₀ e₁ * flattenEntry q p₁ e₀

private theorem sum_det {I : Type*} [Fintype I] (r s u v : I → Scalar) :
    (∑ i,r i*u i)*(∑ i,s i*v i)-(∑ i,r i*v i)*(∑ i,s i*u i) =
      ∑ i,∑ j,r i*s j*(u i*v j-v i*u j) := by
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- No rank assertion is assumed: if two row combinations have a nonzero
ordered determinant, some literal two-row minor was nonzero already. -/
theorem minor_of_card_det (q : Signature Scalar 4) (K₀ K₁ : Mat) (e₀ e₁ : Bool × Bool)
    (h : card 0 q K₀ ![e₀.1,e₀.2] * card 0 q K₁ ![e₁.1,e₁.2] -
      card 0 q K₀ ![e₁.1,e₁.2] * card 0 q K₁ ![e₀.1,e₀.2] ≠ 0) :
    ∃ p₀ p₁ : Bool × Bool, minor q p₀ p₁ e₀ e₁ ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  have hc (K : Mat) (e : Bool × Bool) : card 0 q K ![e.1,e.2] =
      ∑ p : Bool × Bool, K p.1 p.2 * flattenEntry q p e := by
    rw [Fintype.sum_prod_type]
    rfl
  simp only [hc]
  rw [sum_det]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  change K₀ i.1 i.2*K₁ j.1 j.2*minor q i j e₀ e₁=0
  rw [hn i j,mul_zero]

/-- Source nonproportional branch, with the common other-edge parity hypothesis
visible. The output is an actual same-family quaternary retaining p then e. -/
theorem source_compatible_quaternary {m r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (q : Signature Scalar (2*r+4)) (hq : Gadget.Realizes F .disequality q)
    (K₀ K₁ : Mat) (A₀ A₁ : Fin r → Mat) (B₀ B₁ : Mat)
    (α : Fin r → Bool) (hA₀ : ∀ e, HasParity (α e) (A₀ e))
    (hA₁ : ∀ e, HasParity (α e) (A₁ e))
    (β : Bool) (hB₀ : HasParity β B₀) (hB₁ : HasParity β B₁)
    (hline : ¬ ProjectivelyEqual B₁ B₀)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (hcard₀ : card r q K₀ = κ₀ • product r A₀ B₀)
    (hcard₁ : card r q K₁ = κ₁ • product r A₁ B₁) :
    ∃ Q : Signature Scalar 4, Gadget.Realizes F .disequality Q ∧ TraceSequence G r q Q ∧
      ∃ p₀ p₁ : Bool × Bool, minor Q p₀ p₁ (false,β) (true,!β) ≠ 0 := by
  obtain ⟨Q,d₀,d₁,hQ,hseq,hd₀,hd₁,he₀,he₁⟩ := simultaneous_closure hm F G q hq K₀ K₁
    A₀ A₁ B₀ B₁ α hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁ hcard₀ hcard₁
  refine ⟨Q,hQ,hseq,minor_of_card_det Q K₀ K₁ (false,β) (true,!β) ?_⟩
  rw [he₀,he₁]
  simp only [Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply protected_determinant_ne_zero hd₀ hd₁
  exact fun hh => hline ((factorDet_zero_iff hB₀ hB₁).mp hh)

end Holant.Dihedral.CompatibleCoefficientLine
