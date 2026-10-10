import Holant.Dihedral.TwoCardLocalization.DistinctProducts

/-! Actual six-port localization for the different-matching branch, with one
original ancestor, its two original kernels, and an exact representative count. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Certificates
variable {K : Type*} [Field K]

theorem DifferentProducts.nonzero {G : Set (Kernel K)}
    (hG : MatchingContractionClosure.ProjectiveMatrixGroup G) {n : ℕ} {q₀ q₁ : Signature K n}
    (h : DifferentProducts G n q₀ q₁) : q₀ ≠ 0 ∧ q₁ ≠ 0 := by
  obtain ⟨M₀,M₁,h₀,h₁,hs₀,hs₁,rfl,rfl,_⟩ := h
  exact ⟨MatchingContractionClosure.productValue_nonzero _ _ _
      (fun e => MatchingContractionClosure.SafeBinary.nonsingular hG (h₀ e)) hs₀,
    MatchingContractionClosure.productValue_nonzero _ _ _
      (fun e => MatchingContractionClosure.SafeBinary.nonsingular hG (h₁ e)) hs₁⟩

theorem DifferentProducts.scale {G : Set (Kernel K)} {n : ℕ} {q₀ q₁ : Signature K n}
    (h : DifferentProducts G n q₀ q₁) (c : K) (hc : c ≠ 0) :
    DifferentProducts G n (c • q₀) (c • q₁) := by
  obtain ⟨M₀,M₁,h₀,h₁,hs₀,hs₁,rfl,rfl,hd⟩ := h
  refine ⟨{M₀ with scalar := c*M₀.scalar},{M₁ with scalar := c*M₁.scalar},h₀,h₁,
    mul_ne_zero hc hs₀,mul_ne_zero hc hs₁,?_,?_,hd⟩
  all_goals funext x; simp [MatchingContractionClosure.Presentation.tensor,
    MatchingContractionClosure.productValue,Pi.smul_apply,smul_eq_mul,mul_assoc]

/-- Exact different-matching part of source6.6, valid over any field with 2≠0.
The only allowed kernel is the one supplied actual binary, repeated r times.
Both inherited cards remain nonzero, retain different matchings, and arise from
one common program on the original ancestor outside its protected first pair. -/
theorem distinct_actual_core (F : SignatureFamily K) (G : Set (Kernel K))
    (hG : MatchingContractionClosure.ProjectiveMatrixGroup G)
    (hX : (MatchingContractionClosure.X : Kernel K) ∈ G)
    (hrev : MatchingContractionClosure.ReversalStable G)
    (C B : Kernel K) (hC : MatchingContractionClosure.SafeBinary G C)
    (κ : K) (hκ : κ ≠ 0) (hB : Gadget.Realizes F .disequality (binarySignature B))
    (hentries : ∀ a b,B (!a) (!b)=κ*C a b) (htwo : (2:K) ≠ 0)
    (r : ℕ) (f : Signature K (2*r+6)) (hf : Gadget.Realizes F .disequality f)
    (A₀ A₁ : Kernel K) (h : DifferentProducts G (2*r+4)
      (Signature.contract A₀ f) (Signature.contract A₁ f)) :
    ∃ P : Program Unit (2*r+4) 4, ∃ c : K, c ≠ 0 ∧ P.length=r ∧
      Gadget.Realizes F .disequality (c • P.core (fun _ => C) f) ∧
      DifferentProducts G 4 (Signature.contract A₀ (c • P.core (fun _ => C) f))
        (Signature.contract A₁ (c • P.core (fun _ => C) f)) ∧
      Signature.contract A₀ (c • P.core (fun _ => C) f) ≠ 0 ∧
      Signature.contract A₁ (c • P.core (fun _ => C) f) ≠ 0 := by
  obtain ⟨P,hP,hout⟩ := different_products_program G hG hX hrev C hC r _ _ h
  obtain ⟨c,hc,hreal⟩ := P.realizes_core F (fun _ => C) (fun _ => B) (fun _ => κ)
    (fun _ => hκ) (fun _ => hB) (fun _ => hentries) htwo f hf
  have hd : DifferentProducts G 4
      (Signature.contract A₀ (c • P.core (fun _ => C) f))
      (Signature.contract A₁ (c • P.core (fun _ => C) f)) := by
    rw [contract_smul,contract_smul,P.inherited_card,P.inherited_card]
    exact hout.scale c hc
  exact ⟨P,c,hc,hP,hreal,hd,hd.nonzero hG⟩

end Holant.Dihedral.TwoCardLocalization
