import Holant.Dihedral.TwoCardLocalization.RulingObstruction

/-! Two actual nonzero cards of a three-factor current-group product have one
fixed residual factor. Both cases use the literal original product extraction. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
set_option backward.isDefEq.respectTransparency false

def ThreeFactor (m : ℕ) (q : Signature Scalar 6) : Prop :=
  ∃ p : (Fin 3 × Bool) ≃ Fin 6, ∃ A : Fin 3 → Mat, ∃ κ : Scalar,
    (∀ e,A e ∈ groupM m) ∧ κ ≠ 0 ∧ q=MatchingContractionClosure.productValue p A κ

private theorem pairOrder_zero_one {n : ℕ} : pairOrder (0 : Fin (n+2)) 1=Equiv.refl _ := by
  simp [pairOrder]

private theorem oriented_group {m r : ℕ} (hm : 0<m) (A : Fin r → Mat) (σ : Fin r → Bool)
    (hA : ∀ e,A e ∈ groupM m) : ∀ e,MatchingContractionClosure.orientedFactors A σ e ∈ groupM m := by
  intro e
  unfold MatchingContractionClosure.orientedFactors
  split
  · exact transpose_group_mem hm (hA e)
  · exact hA e

private theorem splice_group {m r : ℕ} (hm : 0<m) (A : Fin r → Mat) (C : Mat) (e f : Fin r)
    (hA : ∀ d,A d ∈ groupM m) (hC : C ∈ groupM m) :
    ∀ d,MatchingContractionClosure.spliceFactors C A e f d ∈ groupM m := by
  intro d
  unfold MatchingContractionClosure.spliceFactors
  split
  · exact groupM_mul hm (groupM_mul hm (hA e) hC) (hA f)
  · exact hA d.val

private theorem other_three (e : Fin 3) : ∃ g : Fin 3,g ≠ e := by fin_cases e <;> decide
private theorem third_three (e f : Fin 3) (hef : e ≠ f) : ∃ g : Fin 3,g ≠ e ∧ g ≠ f := by
  fin_cases e <;> fin_cases f <;> first | exact False.elim (hef rfl) | decide

/-- Deleting the selected pair either traces one original factor or fuses two;
the third original factor appears unchanged in BOTH actual residual tables. -/
theorem three_factor_cards_ruling {m : ℕ} (hm : 0<m) (q : Signature Scalar 6)
    (hq : ThreeFactor m q) (C₀ C₁ : Mat) (hC₀ : C₀ ∈ groupM m) (hC₁ : C₁ ∈ groupM m)
    (hn₀ : Signature.contract C₀ q ≠ 0) (hn₁ : Signature.contract C₁ q ≠ 0) :
    RulingPair m (Signature.contract C₀ q) (Signature.contract C₁ q) := by
  obtain ⟨p,A,κ,hA,hκ,rfl⟩ := hq
  let e := (p.symm 0).1
  let f := (p.symm 1).1
  by_cases hef : e=f
  · let σ := MatchingContractionClosure.sameMask p 0
    let p' := (MatchingContractionClosure.flipSlots σ).trans p
    let A' := MatchingContractionClosure.orientedFactors A σ
    have hA' : ∀ d,A' d ∈ groupM m := oriented_group hm A σ hA
    have hp : MatchingContractionClosure.productValue p' A' κ=MatchingContractionClosure.productValue p A κ :=
      MatchingContractionClosure.reorient_product p A κ σ
    obtain ⟨hu,hv⟩ := MatchingContractionClosure.same_selected_ports p (0 : Fin 6) 1 Fin.zero_ne_one hef
    change p' (e,false)=0 at hu
    change p' (e,true)=1 at hv
    have huv : p' (e,false) ≠ p' (e,true) := by rw [hu,hv]; exact Fin.zero_ne_one
    let order := (remainingOrder (p' (e,false)) (p' (e,true)) huv).symm
    have hc (C : Mat) : Signature.contract C (MatchingContractionClosure.productValue p A κ)=
        Tensor.reindex order (MatchingContractionClosure.productValue
          (MatchingContractionClosure.deletePorts p' e) (fun d => A' d.val)
          (MatchingContractionClosure.trace (A' e) C*κ)) := by
      have hh := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_matched p' A' κ e C)
      rw [contractPair_order,hp] at hh
      simpa only [hu,hv,pairOrder_zero_one,Equiv.refl_symm,Tensor.reindex_refl] using hh
    have ht₀ : MatchingContractionClosure.trace (A' e) C₀ ≠ 0 := by
      intro ht
      apply hn₀
      rw [hc]
      funext x
      simp [Tensor.reindex,MatchingContractionClosure.productValue,ht]
    have ht₁ : MatchingContractionClosure.trace (A' e) C₁ ≠ 0 := by
      intro ht
      apply hn₁
      rw [hc]
      funext x
      simp [Tensor.reindex,MatchingContractionClosure.productValue,ht]
    obtain ⟨g,hg⟩ : ∃ g : Fin 3,g ≠ e := other_three e
    have hgood := rulingPair_reindexed (MatchingContractionClosure.deletePorts p' e) order
      (fun d => A' d.val) (fun d => A' d.val)
      (MatchingContractionClosure.trace (A' e) C₀*κ) (MatchingContractionClosure.trace (A' e) C₁*κ)
      (fun d => hA' d.val) (fun d => hA' d.val) (mul_ne_zero ht₀ hκ) (mul_ne_zero ht₁ hκ)
      ⟨g,hg⟩ (ProjectivelyEqual.refl _)
    rw [←hc,←hc] at hgood
    exact hgood
  · let σ := MatchingContractionClosure.crossMask p 0 1
    let p' := (MatchingContractionClosure.flipSlots σ).trans p
    let A' := MatchingContractionClosure.orientedFactors A σ
    have hA' : ∀ d,A' d ∈ groupM m := oriented_group hm A σ hA
    have hp : MatchingContractionClosure.productValue p' A' κ=MatchingContractionClosure.productValue p A κ :=
      MatchingContractionClosure.reorient_product p A κ σ
    obtain ⟨hu,hv⟩ := MatchingContractionClosure.cross_selected_ports p (0 : Fin 6) 1 hef
    change p' (e,true)=0 at hu
    change p' (f,false)=1 at hv
    have huv : p' (e,true) ≠ p' (f,false) := by rw [hu,hv]; exact Fin.zero_ne_one
    let order := (remainingOrder (p' (e,true)) (p' (f,false)) huv).symm
    have hc (C : Mat) : Signature.contract C (MatchingContractionClosure.productValue p A κ)=
        Tensor.reindex order (MatchingContractionClosure.productValue
          (MatchingContractionClosure.splicePorts p' e f) (MatchingContractionClosure.spliceFactors C A' e f) κ) := by
      have hh := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_cross p' A' κ e f hef C)
      rw [contractPair_order,hp] at hh
      simpa only [hu,hv,pairOrder_zero_one,Equiv.refl_symm,Tensor.reindex_refl] using hh
    obtain ⟨g,hge,hgf⟩ : ∃ g : Fin 3,g ≠ e ∧ g ≠ f := third_three e f hef
    have hcommon : ProjectivelyEqual (MatchingContractionClosure.spliceFactors C₁ A' e f ⟨g,hgf⟩)
        (MatchingContractionClosure.spliceFactors C₀ A' e f ⟨g,hgf⟩) := by
      simp only [MatchingContractionClosure.spliceFactors,hge,ite_false]
      exact ProjectivelyEqual.refl _
    have hgood := rulingPair_reindexed (MatchingContractionClosure.splicePorts p' e f) order
      (MatchingContractionClosure.spliceFactors C₀ A' e f) (MatchingContractionClosure.spliceFactors C₁ A' e f)
      κ κ (splice_group hm A' C₀ e f hA' hC₀) (splice_group hm A' C₁ e f hA' hC₁) hκ hκ ⟨g,hgf⟩ hcommon
    rw [←hc,←hc] at hgood
    exact hgood

/-- The precise final non-product assertion of source6.6. -/
theorem disagreement_not_three_factor {m : ℕ} (hm : 0<m) (q : Signature Scalar 6)
    (C₀ C₁ : Mat) (hC₀ : C₀ ∈ groupM m) (hC₁ : C₁ ∈ groupM m)
    (hd : Disagreement m 4 (Signature.contract C₀ q) (Signature.contract C₁ q)) :
    ¬ ThreeFactor m q := by
  intro hq
  obtain ⟨hn₀,hn₁⟩ := hd.nonzero hm
  exact disagreement_not_ruling hm hd (three_factor_cards_ruling hm q hq C₀ C₁ hC₀ hC₁ hn₀ hn₁)

end Holant.Dihedral.TwoCardLocalization
