import Holant.Dihedral.TwoCardLocalization.TaggedSurgery

/-! Complete finite reduction of the common-matching branch: two protected
actual factor lines survive every step, including parity/parity cancellation. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

abbrev PhaseLabel (m : ℕ) := Bool × {t : Scalar // Roots m t}
def phaseKernel {m : ℕ} (i : PhaseLabel m) : Mat := M i.1 i.2.val

private theorem third_edge {s : ℕ} (hs : 2<s) (e f : Fin s) : ∃ g : Fin s,g ≠ e ∧ g ≠ f := by
  classical
  have hc : ({e,f} : Finset (Fin s)).card < (Finset.univ : Finset (Fin s)).card := by
    have h := Finset.card_insert_le e ({f} : Finset (Fin s))
    simp only [Finset.card_singleton,Finset.card_univ,Fintype.card_fin] at h ⊢
    omega
  obtain ⟨g,hg,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨g,by simpa using hnot⟩

private theorem group_parity {m : ℕ} (hm : 0<m) (A : Mat) (h : A ∈ groupM m) :
    ∃ α : Bool,HasParity α A := groupM_isMonomial hm h

theorem two_tags_step {m : ℕ} (hm : 3 ≤ m) (r : ℕ)
    (q₀ q₁ : Signature Scalar (2*(r+1)+4)) (h : TwoTags m _ q₀ q₁) :
    ∃ p : Equiv.Perm (Fin (2*(r+1)+4)), ∃ i : PhaseLabel m,
      TwoTags m (2*r+4) (Signature.contract (phaseKernel i) (Tensor.reindex p.symm q₀))
        (Signature.contract (phaseKernel i) (Tensor.reindex p.symm q₁)) := by
  obtain ⟨s,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,rfl,rfl,e,f,hef,he,hf⟩ := h
  have hs : 2<s := by
    have hh := Fintype.card_congr p
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  obtain ⟨g,hge,hgf⟩ := third_edge hs e f
  obtain ⟨β₀,hB₀⟩ := group_parity (by omega) (A₀ g) (hA₀ g)
  obtain ⟨β₁,hB₁⟩ := group_parity (by omega) (A₁ g) (hA₁ g)
  by_cases hb : β₁=β₀
  · subst β₁
    obtain ⟨t,ht₀,ht₁⟩ := compatible_trace hm hB₀ hB₁
    refine ⟨pairOrder (p (g,false)) (p (g,true)),(β₀,t),?_⟩
    exact trace_two_tags p A₀ A₁ κ₀ κ₁ hA₀ hA₁ hκ₀ hκ₁ e f g hef hge.symm hgf.symm he hf _ ht₀ ht₁
  · have hb' : β₁=(!β₀) := by cases β₀ <;> cases β₁ <;> simp_all
    subst β₁
    obtain ⟨α₀,he₀⟩ := group_parity (by omega) (A₀ e) (hA₀ e)
    obtain ⟨α₁,he₁⟩ := group_parity (by omega) (A₁ e) (hA₁ e)
    obtain ⟨t,ht⟩ := absorb_parity_discrepancy hm α₀ α₁ β₀ (A₀ e) (A₁ e) (A₀ g) (A₁ g) he₀ he₁ hB₀ hB₁
    refine ⟨pairOrder (p (e,true)) (p (g,false)),(false,t),?_⟩
    exact cross_two_tags (by omega) p A₀ A₁ κ₀ κ₁ hA₀ hA₁ hκ₀ hκ₁ e f g hef hge.symm hgf.symm hf _
      (M_mem_group (by omega) false t.property) ht

/-- Exactly r actual group representatives are selected for the common-matching
branch on 2r+4 residual ports; neither selected protected line is lost. -/
theorem two_tags_program {m : ℕ} (hm : 3 ≤ m) (r : ℕ)
    (q₀ q₁ : Signature Scalar (2*r+4)) (h : TwoTags m _ q₀ q₁) :
    ∃ P : Program (PhaseLabel m) (2*r+4) 4, P.length=r ∧
      TwoTags m 4 (P.residual phaseKernel q₀) (P.residual phaseKernel q₁) :=
  reduce_invariant phaseKernel (TwoTags m) (two_tags_step hm) r q₀ q₁ h

/-- With four residual ports there are exactly two factors, and BOTH literal
ordered factor lines differ. This is the precise source terminal alternative. -/
theorem two_tags_four_exact {m : ℕ} {q₀ q₁ : Signature Scalar 4} (h : TwoTags m 4 q₀ q₁) :
    ∃ p : (Fin 2 × Bool) ≃ Fin 4, ∃ A₀ A₁ : Fin 2 → Mat, ∃ κ₀ κ₁ : Scalar,
      (∀ e,A₀ e ∈ groupM m) ∧ (∀ e,A₁ e ∈ groupM m) ∧ κ₀ ≠ 0 ∧ κ₁ ≠ 0 ∧
      q₀=MatchingContractionClosure.productValue p A₀ κ₀ ∧
      q₁=MatchingContractionClosure.productValue p A₁ κ₁ ∧
      ∀ e,¬ ProjectivelyEqual (A₁ e) (A₀ e) := by
  obtain ⟨s,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,hq₀,hq₁,e,f,hef,he,hf⟩ := h
  have hs : s=2 := by
    have hh := Fintype.card_congr p
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  subst s
  refine ⟨p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,hq₀,hq₁,?_⟩
  intro d
  have hd : d=e ∨ d=f := by fin_cases d <;> fin_cases e <;> fin_cases f <;> simp_all
  rcases hd with rfl|rfl
  · exact he
  · exact hf

end Holant.Dihedral.TwoCardLocalization
