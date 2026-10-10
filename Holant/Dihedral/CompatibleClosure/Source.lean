import Holant.Dihedral.CompatibleClosure.PhysicalPair
import Holant.Dihedral.CompatibleClosure.CycleProducts
import Holant.Dihedral.CompatibleClosure.PairOrder

/-! Source Lemma 6.4: simultaneous physical compatible closure and original
matching-edge shortening, derived from full products and actual representatives.
All gadget scalars, including an optional deleted-circle factor, are recorded. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Dihedral.EndpointParallelogram

private theorem port_distinct {r n : ℕ} (p : (Fin r × Bool) ≃ Fin n) (e : Fin r) :
    p (e,false) ≠ p (e,true) := by
  intro he
  have hh := congrArg Prod.snd (p.injective he)
  cases hh

/-- Common untagged factors of the two actual products can be closed with one
actual group representative while both physical outputs remain nonzero. -/
theorem source_compatible_closure {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e₀ e₁ : Fin r) (hcommon : ProjectivelyEqual (A₁ e₁) (A₀ e₀))
    (hu : p₁ (e₁,false) = p₀ (e₀,false)) (hv : p₁ (e₁,true) = p₀ (e₀,true))
    (hq₀ : Gadget.Realizes F .disequality (productValue p₀ A₀ κ₀))
    (hq₁ : Gadget.Realizes F .disequality (productValue p₁ A₁ κ₁)) :
    ∃ γ : Bool, ∃ t : {t : Scalar // Roots m t},
      trace (A₀ e₀) (M γ t.val) ≠ 0 ∧ trace (A₁ e₁) (M γ t.val) ≠ 0 ∧
      Nonempty (PhysicalPair F G (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁)
        (pairOrder (p₀ (e₀,false)) (p₀ (e₀,true))) γ t) := by
  obtain ⟨γ,t,ht,ht₀,ht₁⟩ := untagged_trace_phase hm _ _ (hA₀ e₀) hcommon
  let order := pairOrder (p₀ (e₀,false)) (p₀ (e₀,true))
  have horder₀ : order 0 = p₀ (e₀,false) := pairOrder_first _ _ (port_distinct p₀ e₀)
  have horder₁ : order 1 = p₀ (e₀,true) := pairOrder_second _ _
  have hn₀ := close_product_edge_nonzero p₀ A₀ (fun e => groupM_isMonomial (by omega) (hA₀ e)) hκ₀ e₀ _ ht₀
  have hn₁ := close_product_edge_nonzero p₁ A₁ (fun e => groupM_isMonomial (by omega) (hA₁ e)) hκ₁ e₁ _ ht₁
  refine ⟨γ,⟨t,ht⟩,ht₀,ht₁,physical_pair F G _ _ order hq₀ hq₁ γ ⟨t,ht⟩ ?_ ?_⟩
  · apply full_close_nonzero order
    simpa only [horder₀,horder₁] using hn₀
  · apply full_close_nonzero order
    simpa only [horder₀,horder₁,hu,hv] using hn₁

/-- Closing an edge of M0 absent from M1 performs one actual cancellation-free
cycle shortening on both original matching products. The selected phase comes
from the full current finite root group, never from an assumed good-phase oracle. -/
theorem source_cycle_shortening {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e₀ : Fin r)
    (hd : (Pairing.ofPorts p₁).mate (p₀ (e₀,false)) ≠ p₀ (e₀,true))
    (hq₀ : Gadget.Realizes F .disequality (productValue p₀ A₀ κ₀))
    (hq₁ : Gadget.Realizes F .disequality (productValue p₁ A₁ κ₁)) :
    ∃ γ : Bool, ∃ t : {t : Scalar // Roots m t},
      Nonempty (PhysicalPair F G (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁)
        (pairOrder (p₀ (e₀,false)) (p₀ (e₀,true))) γ t) ∧
      (p₁.symm (p₀ (e₀,false))).1 ≠ (p₁.symm (p₀ (e₀,true))).1 ∧
      Fintype.card (Remaining (p₀ (e₀,false)) (p₀ (e₀,true))) = n := by
  obtain ⟨γ,t,ht,hn₀,hn₁⟩ := shorten_different_products hm p₀ p₁ A₀ A₁ hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁ e₀ hd
  let order := pairOrder (p₀ (e₀,false)) (p₀ (e₀,true))
  have horder₀ : order 0 = p₀ (e₀,false) := pairOrder_first _ _ (port_distinct p₀ e₀)
  have horder₁ : order 1 = p₀ (e₀,true) := pairOrder_second _ _
  refine ⟨γ,⟨t,ht⟩,physical_pair F G _ _ order hq₀ hq₁ γ ⟨t,ht⟩ ?_ ?_,
    different_edge_indices p₁ _ _ (port_distinct p₀ e₀) hd,?_⟩
  · apply full_close_nonzero order
    simpa only [horder₀,horder₁] using hn₀
  · apply full_close_nonzero order
    simpa only [horder₀,horder₁] using hn₁
  · have hh := exactly_two_ports_removed (p₀ (e₀,false)) (p₀ (e₀,true)) (port_distinct p₀ e₀)
    simpa using Nat.add_right_cancel (by simpa only [Fintype.card_fin] using hh.symm)

end Holant.Dihedral.CompatibleClosure
