import Holant.Dihedral.SectorRuling.Alignment

/-! Full source Lemma6.8, sector-ruling rigidity. Only the literal sampled
zero-or-current-group matching condition is assumed. Empty, zero and
proportional pencils are included, and the finite m=3 obstruction is retained
in the proved support step. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Certificates Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

def standardPorts (s : ℕ) : (Fin s × Bool) ≃ Fin (2*s) :=
  (Equiv.prodCongr (Equiv.refl _) boolIndex).trans (finProdFinEquiv.trans (finCongr (by omega)))

structure RulingData (m s : ℕ) (U V : Signature Scalar (2*s)) where
  ports : (Fin s × Bool) ≃ Fin (2*s)
  fixed : Fin s → Mat
  fixed_mem : ∀ e,fixed e ∈ groupM m
  varying : Option (Fin s)
  samples : ∀ t : Scalar,Roots m t → tensorPencil U V t=0 ∨
    ∃ A : Fin s → Mat,∃ κ : Scalar,(∀ e,A e ∈ groupM m) ∧ κ ≠ 0 ∧
      tensorPencil U V t=MatchingContractionClosure.productValue ports A κ ∧
      ∀ e,varying ≠ some e → ProjectivelyEqual (A e) (fixed e)

private theorem zero_port_ruling {m : ℕ} (hm : 3 ≤ m) (U V : Signature Scalar (2*0))
    (hs : ∀ t : Scalar,Roots m t → tensorPencil U V t=0 ∨ MatchingSample m 0 (tensorPencil U V t)) :
    Nonempty (RulingData m 0 U V) := by
  refine ⟨⟨standardPorts 0,fun _ => M false 1,fun e => M_mem_group (by omega) false (Roots.one m),none,?_⟩⟩
  intro t ht
  rcases hs t ht with hz|⟨p,A,κ,hA,hκ,hq⟩
  · exact Or.inl hz
  · right
    have hp : p=standardPorts 0 := by apply Equiv.ext; rintro ⟨e,b⟩; exact Fin.elim0 e
    refine ⟨A,κ,hA,hκ,?_,fun e => Fin.elim0 e⟩
    simpa only [hp] using hq

/-- The one-varying-factor conclusion is derived from three literal products;
the third product may be zero. The remaining phases are then handled by the
proved fixed-factor-in-span lemma, including endpoint/proportional cases. -/
private theorem positive_ruling {m r : ℕ} (hm : 3 ≤ m) (U V : Signature Scalar (2*(r+1)))
    (hs : ∀ t : Scalar,Roots m t → tensorPencil U V t=0 ∨ MatchingSample m (r+1) (tensorPencil U V t)) :
    Nonempty (RulingData m (r+1) U V) := by
  classical
  by_cases hex : ∃ a : Scalar,Roots m a ∧ tensorPencil U V a ≠ 0
  · obtain ⟨a,ha,hna⟩ := hex
    obtain ⟨p,A₀,κ₀,hA₀,hκ₀,hq₀⟩ := (hs a ha).resolve_left hna
    obtain ⟨b,hb,hab,hnb⟩ := two_nonzero_samples hm U V a ha hna
    have rep := common_representation hm U V hs a ha hna p A₀ κ₀ hA₀ hκ₀ hq₀
    obtain ⟨A₁,κ₁,hA₁,hκ₁,hq₁⟩ := rep b hb hnb
    have hsupport := source_common_support hm U V hs a b ha hb hna hnb
    rw [hq₀,hq₁] at hsupport
    obtain ⟨α,hα⟩ := shared_parities p A₀ A₁ κ₀ κ₁
      (fun e => groupM_isMonomial (by omega) (hA₀ e))
      (fun e => groupM_isMonomial (by omega) (hA₁ e)) hκ₀ hsupport
    obtain ⟨c,hc,hca,hcb⟩ := third_root hm a b ha hb
    obtain ⟨A₂,κ₂,hq₂⟩ : ∃ A₂ : Fin (r+1) → Mat,∃ κ₂ : Scalar,
        tensorPencil U V c=MatchingContractionClosure.productValue p A₂ κ₂ := by
      rcases hs c hc with hz|hd
      · refine ⟨A₀,0,?_⟩
        rw [hz]
        funext x
        simp [MatchingContractionClosure.productValue]
      · obtain ⟨A₂,κ₂,hA₂,hκ₂,hq₂⟩ := rep c hc (hd.nonzero (by omega))
        exact ⟨A₂,κ₂,hq₂⟩
    have span (t : Scalar) (A : Fin (r+1) → Mat) (κ : Scalar)
        (hq : tensorPencil U V t=MatchingContractionClosure.productValue p A κ) :
        MatchingContractionClosure.productValue p A κ=
          combination ((b-t)/(b-a)) ((t-a)/(b-a))
            (MatchingContractionClosure.productValue p A₀ κ₀) (MatchingContractionClosure.productValue p A₁ κ₁) := by
      rw [←hq,tensor_interpolation U V a b t hab,hq₀,hq₁]
    have hn₀ : (b-c)/(b-a) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hcb.symm) (sub_ne_zero.mpr hab.symm)
    have hn₁ : (c-a)/(b-a) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hab.symm)
    obtain ⟨varying,hvarying⟩ := three_products_one_factor p A₀ A₁ A₂ κ₀ κ₁ κ₂ _ _ hκ₀ hκ₁ hn₀ hn₁
      α (fun e => (hα e).1) (fun e => (hα e).2) (span c A₂ κ₂ hq₂)
    refine ⟨⟨p,A₀,hA₀,varying,?_⟩⟩
    intro t ht
    by_cases hz : tensorPencil U V t=0
    · exact Or.inl hz
    · obtain ⟨A,κ,hA,hκ,hq⟩ := rep t ht hz
      refine Or.inr ⟨A,κ,hA,hκ,hq,?_⟩
      intro e he
      exact fixed_factor_in_span p A₀ A₁ A κ₀ κ₁ κ _ _
        (fun e => groupM_isMonomial (by omega) (hA e)) hκ (span t A κ hq) e (hvarying e he)
  · refine ⟨⟨standardPorts (r+1),fun _ => M false 1,
      fun _ => M_mem_group (by omega) false (Roots.one m),none,?_⟩⟩
    intro t ht
    left
    by_contra hn
    exact hex ⟨t,ht,hn⟩

/-- Lemma6.8: every nonzero finite-root sample has one fixed original matching
and all but at most one binary factor line fixed projectively. No ruling or
common support appears in the hypotheses. -/
theorem source_sector_ruling {m s : ℕ} (hm : 3 ≤ m) (U V : Signature Scalar (2*s))
    (hs : ∀ t : Scalar,Roots m t → tensorPencil U V t=0 ∨ MatchingSample m s (tensorPencil U V t)) :
    Nonempty (RulingData m s U V) := by
  cases s with
  | zero => exact zero_port_ruling hm U V hs
  | succ r => exact positive_ruling hm U V hs

end Holant.Dihedral.SectorRuling
