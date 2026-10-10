import Holant.Dihedral.CompatibleClosure.CrossProducts
import Holant.Dihedral.CompatibleClosure.Representatives
import Holant.Dihedral.CompatibleClosure.SourceProtected
import Holant.Dihedral.CompatibleClosure.SplicedOutput
import Holant.Dihedral.CompatibleClosure.Batch
import Holant.Dihedral.CompatibleClosure.GroupFusion

/-! Main-text Lemma 6.4 in the source fixed actual transfer-representative
interface. Physical connection normalization is derived from B_g X=kappa_g T_g;
all original products, ports, representative scalars and circle factors remain. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Dihedral.EndpointParallelogram

theorem source_compatible_closure_from_transfer {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e₀ e₁ : Fin r) (hcommon : ProjectivelyEqual (A₁ e₁) (A₀ e₀))
    (hu : p₁ (e₁,false) = p₀ (e₀,false)) (hv : p₁ (e₁,true) = p₀ (e₀,true))
    (hq₀ : Gadget.Realizes F .disequality (productValue p₀ A₀ κ₀))
    (hq₁ : Gadget.Realizes F .disequality (productValue p₁ A₁ κ₁)) :
    ∃ γ : Bool, ∃ t : {t : Scalar // Roots m t},
      trace (A₀ e₀) (M γ t.val) ≠ 0 ∧ trace (A₁ e₁) (M γ t.val) ≠ 0 ∧
      Nonempty (PhysicalPair F (G.connections (by omega)) (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁)
        (pairOrder (p₀ (e₀,false)) (p₀ (e₀,true))) γ t) :=
  source_compatible_closure hm F (G.connections (by omega)) p₀ p₁ A₀ A₁ hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁ e₀ e₁ hcommon hu hv hq₀ hq₁

theorem source_cycle_shortening_from_transfer {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e₀ : Fin r)
    (hd : (Pairing.ofPorts p₁).mate (p₀ (e₀,false)) ≠ p₀ (e₀,true))
    (hq₀ : Gadget.Realizes F .disequality (productValue p₀ A₀ κ₀))
    (hq₁ : Gadget.Realizes F .disequality (productValue p₁ A₁ κ₁)) :
    ∃ γ : Bool, ∃ t : {t : Scalar // Roots m t},
      Nonempty (PhysicalPair F (G.connections (by omega)) (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁)
        (pairOrder (p₀ (e₀,false)) (p₀ (e₀,true))) γ t) ∧
      (p₁.symm (p₀ (e₀,false))).1 ≠ (p₁.symm (p₀ (e₀,true))).1 ∧
      Fintype.card (Remaining (p₀ (e₀,false)) (p₀ (e₀,true))) = n :=
  source_cycle_shortening hm F (G.connections (by omega)) p₀ p₁ A₀ A₁ hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁ e₀ hd hq₀ hq₁

theorem source_cross_closure_from_transfer {m n r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (e₀ f₀ e₁ f₁ : Fin r) (hef₀ : e₀ ≠ f₀) (hef₁ : e₁ ≠ f₁)
    (hu : p₁ (e₁,true) = p₀ (e₀,true)) (hv : p₁ (f₁,false) = p₀ (f₀,false))
    (hq₀ : Gadget.Realizes F .disequality (productValue p₀ A₀ κ₀))
    (hq₁ : Gadget.Realizes F .disequality (productValue p₁ A₁ κ₁))
    (γ : Bool) (t : {t : Scalar // Roots m t}) :
    Nonempty (PhysicalPair F (G.connections (by omega)) (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁)
      (pairOrder (p₀ (e₀,true)) (p₀ (f₀,false))) γ t) :=
  source_cross_closure hm F (G.connections (by omega)) p₀ p₁ A₀ A₁ hA₀ hA₁ κ₀ κ₁ hκ₀ hκ₁ e₀ f₀ e₁ f₁ hef₀ hef₁ hu hv hq₀ hq₁ γ t

end Holant.Dihedral.CompatibleClosure
