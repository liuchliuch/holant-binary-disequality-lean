import Holant.Dihedral.SectorRuling.ProductFaces

/-! The Segre-line criterion is proved from literal coefficient minors of the
three full matching products; no one-factor ruling is supplied as an input. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false
variable {s n : ℕ}

theorem shared_parities (p : (Fin s × Bool) ≃ Fin n) (A₀ A₁ : Fin s → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,IsMonomial (A₀ e)) (hA₁ : ∀ e,IsMonomial (A₁ e)) (hκ₀ : κ₀ ≠ 0)
    (hs : support (coefficients (MatchingContractionClosure.productValue p A₀ κ₀))=
      support (coefficients (MatchingContractionClosure.productValue p A₁ κ₁))) :
    ∃ α : Fin s → Bool,∀ e,HasParity (α e) (A₀ e) ∧ HasParity (α e) (A₁ e) := by
  choose α w hw he using hA₀
  let x := matchingWord p α (fun _ => false)
  have hx₀ e : A₀ e (x (p (e,false))) (x (p (e,true))) ≠ 0 := by
    rw [he e]
    simp [x,matchingWord,monomial,hw]
  have hq₀ : MatchingContractionClosure.productValue p A₀ κ₀ x ≠ 0 :=
    mul_ne_zero hκ₀ (Finset.prod_ne_zero_iff.mpr (fun e _ => hx₀ e))
  have hsupport := Finset.ext_iff.mp hs (EndpointParallelogram.bitsEquiv (Fin n) x)
  simp only [mem_support,coefficients,Equiv.symm_apply_apply] at hsupport
  have hq₁ := hsupport.mp hq₀
  have hx₁ e := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hq₁).2) e (Finset.mem_univ e)
  refine ⟨α,fun e => ⟨⟨w e,hw e,he e⟩,?_⟩⟩
  have hn : A₁ e false (α e) ≠ 0 := by simpa [x,matchingWord] using hx₁ e
  obtain ⟨β,v,hv,hB⟩ := hA₁ e
  have hα : α e=β := by
    by_contra hh
    rw [hB] at hn
    simp [monomial,hh] at hn
  subst β
  exact ⟨v,hv,hB⟩

/-- Two independent nonzero linear coefficients and a third simple product
force the two endpoint products to differ in at most one actual factor line. -/
theorem three_products_one_factor (p : (Fin s × Bool) ≃ Fin n) (A₀ A₁ A₂ : Fin s → Mat)
    (κ₀ κ₁ κ₂ a b : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (α : Fin s → Bool) (hA₀ : ∀ e,HasParity (α e) (A₀ e)) (hA₁ : ∀ e,HasParity (α e) (A₁ e))
    (heq : MatchingContractionClosure.productValue p A₂ κ₂ =
      combination a b (MatchingContractionClosure.productValue p A₀ κ₀) (MatchingContractionClosure.productValue p A₁ κ₁)) :
    ∃ varying : Option (Fin s),∀ e,varying ≠ some e → ProjectivelyEqual (A₁ e) (A₀ e) := by
  classical
  let x := matchingWord p α (fun _ => false)
  have hx (A : Fin s → Mat) (hA : ∀ e,HasParity (α e) (A e)) (e : Fin s) :
      A e (x (p (e,false))) (x (p (e,true))) ≠ 0 := by
    obtain ⟨w,hw,he⟩ := hA e
    rw [he]
    simp [x,matchingWord,monomial,hw]
  have hout (A : Fin s → Mat) (hA : ∀ e,HasParity (α e) (A e)) (κ : Scalar) (hκ : κ ≠ 0) (e f : Fin s) :
      outsideProduct p A κ e f x ≠ 0 :=
    mul_ne_zero hκ (Finset.prod_ne_zero_iff.mpr (fun d _ => hx A hA d))
  have hpair (e f : Fin s) (hef : e ≠ f) : ProjectivelyEqual (A₁ e) (A₀ e) ∨ ProjectivelyEqual (A₁ f) (A₀ f) := by
    by_cases he : ProjectivelyEqual (A₁ e) (A₀ e)
    · exact Or.inl he
    right
    by_contra hf
    have hde : factorDet (α e) (A₀ e) (A₁ e) ≠ 0 := fun h => he ((factorDet_zero_iff (hA₀ e) (hA₁ e)).mp h)
    have hdf : factorDet (α f) (A₀ f) (A₁ f) ≠ 0 := fun h => hf ((factorDet_zero_iff (hA₀ f) (hA₁ f)).mp h)
    have hz := product_faceDet_zero p A₂ κ₂ e f hef (α e) (α f) x
    rw [heq,combination_faceDet p A₀ A₁ κ₀ κ₁ a b e f hef (α e) (α f) x] at hz
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb)
      (hout A₀ hA₀ κ₀ hκ₀ e f)) (hout A₁ hA₁ κ₁ hκ₁ e f)) hde) hdf hz
  by_cases hall : ∀ e,ProjectivelyEqual (A₁ e) (A₀ e)
  · exact ⟨none,fun e _ => hall e⟩
  · push_neg at hall
    obtain ⟨e,he⟩ := hall
    refine ⟨some e,?_⟩
    intro f hef
    have hne : e ≠ f := fun h => hef (congrArg some h)
    exact (hpair e f hne).resolve_left he

/-- A fixed endpoint factor line remains fixed in EVERY nonzero matching
product on their span. The coefficient is derived from actual complementary
entries, so zero endpoints and vanishing interpolation coefficients are allowed. -/
theorem fixed_factor_in_span (p : (Fin s × Bool) ≃ Fin n) (A₀ A₁ A₂ : Fin s → Mat)
    (κ₀ κ₁ κ₂ a b : Scalar) (hA₂ : ∀ e,IsMonomial (A₂ e)) (hκ₂ : κ₂ ≠ 0)
    (heq : MatchingContractionClosure.productValue p A₂ κ₂ =
      combination a b (MatchingContractionClosure.productValue p A₀ κ₀) (MatchingContractionClosure.productValue p A₁ κ₁))
    (e : Fin s) (he : ProjectivelyEqual (A₁ e) (A₀ e)) : ProjectivelyEqual (A₂ e) (A₀ e) := by
  classical
  obtain ⟨c,hc,hcEq⟩ := he
  let x := supportedWord p A₂ hA₂
  let R := fun (A : Fin s → Mat) (κ : Scalar) => κ*∏ d ∈ ({e}ᶜ : Finset (Fin s)),
    A d (x (p (d,false))) (x (p (d,true)))
  let T := a*R A₀ κ₀+b*c*R A₁ κ₁
  have hR : R A₂ κ₂ ≠ 0 := mul_ne_zero hκ₂
    (Finset.prod_ne_zero_iff.mpr (fun d _ => supportedWord_factor p A₂ hA₂ d))
  have hv (u v : Bool) : A₂ e u v*R A₂ κ₂=A₀ e u v*T := by
    have h := congrFun heq (MatchingContractionClosure.insertPair (p (e,false)) (p (e,true)) u v x)
    simp only [combination,MatchingContractionClosure.product_extract_edge] at h
    rw [hcEq] at h
    change A₂ e u v*R A₂ κ₂=a*(A₀ e u v*R A₀ κ₀)+b*(c*A₀ e u v*R A₁ κ₁) at h
    rw [h]
    simp only [T]
    ring
  have hT : T ≠ 0 := by
    have hn := mul_ne_zero (supportedWord_factor p A₂ hA₂ e) hR
    rw [hv] at hn
    exact (mul_ne_zero_iff.mp hn).2
  refine ⟨T/R A₂ κ₂,div_ne_zero hT hR,?_⟩
  funext u v
  change A₂ e u v=(T/R A₂ κ₂)*A₀ e u v
  field_simp [hR]
  linear_combination hv u v

end Holant.Dihedral.SectorRuling
