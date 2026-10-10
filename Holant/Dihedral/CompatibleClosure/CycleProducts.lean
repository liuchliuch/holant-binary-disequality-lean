import Holant.Dihedral.CompatibleClosure.GlobalTrace
import Holant.Dihedral.CompatibleClosure.SelectedEdges

/-! A genuinely different original matching edge yields one simultaneous
nonzero trace/splice operation on the two full actual coefficient products. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Dihedral.EndpointParallelogram

/-- The edge discrepancy itself selects and orients the two other factors;
the source local cross-product hypothesis is not supplied by the caller. -/
theorem shorten_different_products {n r m : ℕ} (hm : 3 ≤ m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin n) (A₀ A₁ : Fin r → Mat)
    (hA₀ : ∀ e, A₀ e ∈ groupM m) (hA₁ : ∀ e, A₁ e ∈ groupM m)
    (κ₀ κ₁ : Scalar) (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e₀ : Fin r)
    (hd : (Pairing.ofPorts p₁).mate (p₀ (e₀,false)) ≠ p₀ (e₀,true)) :
    ∃ γ t, Roots m t ∧
      (fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b *
        productValue p₀ A₀ κ₀ (insertPair (p₀ (e₀,false)) (p₀ (e₀,true)) a b x)) ≠ 0 ∧
      (fun x => ∑ a : Bool, ∑ b : Bool, M γ t a b *
        productValue p₁ A₁ κ₁ (insertPair (p₀ (e₀,false)) (p₀ (e₀,true)) a b x)) ≠ 0 := by
  let u := p₀ (e₀,false)
  let v := p₀ (e₀,true)
  have huv : u ≠ v := by
    intro he
    have hh := congrArg Prod.snd (p₀.injective he)
    cases hh
  have hef := different_edge_indices p₁ u v huv hd
  let B : Fin r → Mat := fun e => if selectMask p₁ u v e then Kernel.transpose (A₁ e) else A₁ e
  have hB : ∀ e, IsMonomial (B e) := by
    intro e
    dsimp only [B]
    split_ifs
    · exact (groupM_isMonomial (by omega) (hA₁ e)).transpose
    · exact groupM_isMonomial (by omega) (hA₁ e)
  have hp : productValue (selectedPorts p₁ u v) B κ₁ = productValue p₁ A₁ κ₁ :=
    reorient_product p₁ A₁ κ₁ (selectMask p₁ u v)
  obtain ⟨γ,t,ht,htrace,_⟩ := untagged_trace_phase hm (A₀ e₀) (A₀ e₀)
    (hA₀ e₀) (ProjectivelyEqual.refl _)
  have hn := close_product_two_nonzero (selectedPorts p₁ u v) B hB hκ₁
    (p₁.symm u).1 (p₁.symm v).1 hef (M γ t) (M_isMonomial γ (ht.ne_zero (by omega)))
  obtain ⟨hu,hv⟩ := selected_endpoints p₁ u v huv hd
  rw [hu,hv,hp] at hn
  exact ⟨γ,t,ht,
    close_product_edge_nonzero p₀ A₀ (fun e => groupM_isMonomial (by omega) (hA₀ e)) hκ₀ e₀ _ htrace,hn⟩

end Holant.Dihedral.CompatibleClosure
