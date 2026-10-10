import Holant.Dihedral.TwoCardLocalization.Localization
import Holant.Dihedral.EndpointParallelogram.Factors

/-! Nonzero complete monomial products determine their original matching and,
when the matching is aligned, every ordered binary factor line. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.EndpointParallelogram
set_option backward.isDefEq.respectTransparency false

private theorem bit_xor (a b c : Bool) :
    bitEquiv b=bitEquiv a+bitEquiv c ↔ b=(a ^^ c) := by cases a <;> cases b <;> cases c <;> decide

theorem product_cardMatching {n r : ℕ} (p : (Fin r × Bool) ≃ Fin n) (A : Fin r → Mat)
    (κ : Scalar) (hA : ∀ e,IsMonomial (A e)) (hκ : κ ≠ 0) :
    ∃ offset : Fin n → ZMod 2,
      CardMatching (MatchingContractionClosure.productValue p A κ) (Pairing.ofPorts p) offset := by
  choose α w hw he using hA
  have hp : MatchingContractionClosure.productValue p A κ =
      monomialProduct p (fun e => bitEquiv (α e)) w κ := by
    funext x
    apply congrArg (κ * ·)
    apply Finset.prod_congr rfl
    intro e _
    rw [he e]
    simp only [monomial,bit_xor]
  exact ⟨matchingOffset p (fun e => bitEquiv (α e)),
    hp ▸ monomialProduct_matching p (fun e => bitEquiv (α e)) w κ hw hκ⟩

/-- This uniqueness uses only the actual support cosets, retaining arbitrary
nonzero original coefficients, scales and both monomial parities. -/
theorem product_matching_unique {n r s : ℕ} (p₀ : (Fin r × Bool) ≃ Fin n) (p₁ : (Fin s × Bool) ≃ Fin n)
    (A₀ : Fin r → Mat) (A₁ : Fin s → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,IsMonomial (A₀ e)) (hA₁ : ∀ e,IsMonomial (A₁ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (he : MatchingContractionClosure.productValue p₀ A₀ κ₀ = MatchingContractionClosure.productValue p₁ A₁ κ₁) :
    Pairing.ofPorts p₀=Pairing.ofPorts p₁ := by
  obtain ⟨a,ha⟩ := product_cardMatching p₀ A₀ κ₀ hA₀ hκ₀
  obtain ⟨b,hb⟩ := product_cardMatching p₁ A₁ κ₁ hA₁ hκ₁
  apply Pairing.code_injective
  apply coset_direction_unique _ _ a b
  ext x
  exact (ha x).symm.trans ((congrArg (fun q => q ((bitsEquiv (Fin n)).symm x) ≠ 0) he) ▸ hb x)

/-- Equality of complete nonzero products forces each actual ordered factor
line to agree. The quotient scalar is constructed from complementary entries. -/
theorem product_factor_line_unique {n r : ℕ} (p : (Fin r × Bool) ≃ Fin n) (A₀ A₁ : Fin r → Mat)
    (κ₀ κ₁ : Scalar) (hA₁ : ∀ e,IsMonomial (A₁ e)) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (he : MatchingContractionClosure.productValue p A₀ κ₀ = MatchingContractionClosure.productValue p A₁ κ₁)
    (e : Fin r) : ProjectivelyEqual (A₁ e) (A₀ e) := by
  let x := supportedWord p A₁ hA₁
  have hx₁ d : A₁ d (x (p (d,false))) (x (p (d,true))) ≠ 0 := supportedWord_factor p A₁ hA₁ d
  have hv₁ : MatchingContractionClosure.productValue p A₁ κ₁ x ≠ 0 :=
    mul_ne_zero hκ₁ (Finset.prod_ne_zero_iff.mpr (fun d _ => hx₁ d))
  have hv₀ : MatchingContractionClosure.productValue p A₀ κ₀ x ≠ 0 := by rw [he]; exact hv₁
  have hx₀ d : A₀ d (x (p (d,false))) (x (p (d,true))) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hv₀).2) d (Finset.mem_univ d)
  let L := κ₀*∏ d ∈ ({e}ᶜ : Finset (Fin r)),A₀ d (x (p (d,false))) (x (p (d,true)))
  let R := κ₁*∏ d ∈ ({e}ᶜ : Finset (Fin r)),A₁ d (x (p (d,false))) (x (p (d,true)))
  have hL : L ≠ 0 := mul_ne_zero hκ₀ (Finset.prod_ne_zero_iff.mpr (fun d _ => hx₀ d))
  have hR : R ≠ 0 := mul_ne_zero hκ₁ (Finset.prod_ne_zero_iff.mpr (fun d _ => hx₁ d))
  refine ⟨L/R,div_ne_zero hL hR,?_⟩
  funext a b
  have hh := congrFun he (MatchingContractionClosure.insertPair (p (e,false)) (p (e,true)) a b x)
  rw [MatchingContractionClosure.product_extract_edge,MatchingContractionClosure.product_extract_edge] at hh
  change A₀ e a b*L=A₁ e a b*R at hh
  change A₁ e a b=(L/R)*A₀ e a b
  field_simp [hR]
  linear_combination -hh

end Holant.Dihedral.TwoCardLocalization
