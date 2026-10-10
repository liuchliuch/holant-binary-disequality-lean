import Holant.Pauli.ExoticKlein.FiberVariation
import Holant.Pauli.ExoticKlein.FiberOrientation

/-! Actual eight-port obstruction before any affine normalization. The two
original endpoint orders give the fused maps p+q and theta(p)+q. Their exact
nonzero scalar weights are retained by the physical fiber surgery. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant.Certificates.MatchingContractionClosure
open MatchingCard
namespace Fiber
variable {P : Type*} [Fintype P] [LinearOrder P]

def survivorIndex (i : Fin 4) (hi : i ≠ 2) : Fin (Fintype.card (OtherEdges (2 : Fin 4))) :=
  Fintype.equivFin (OtherEdges (2 : Fin 4)) ⟨i,hi⟩

theorem survivorIndex_injective (i j : Fin 4) (hi : i ≠ 2) (hj : j ≠ 2)
    (he : survivorIndex i hi = survivorIndex j hj) : i = j :=
  congrArg Subtype.val ((Fintype.equivFin (OtherEdges (2 : Fin 4))).injective he)

theorem fused_at_survivor (labels : Label → Fin 4 → Label) (a : Label) (i : Fin 4) (hi : i ≠ 2) :
    fusedLabels 1 2 0 labels a (survivorIndex i hi) =
      if i = 1 then labels a 1+labels a 2 else labels a i := by
  simp only [fusedLabels,survivorIndex,Equiv.symm_apply_apply,MatchingCard.spliceLabel,theta_zero,add_zero]

theorem fused_variation_obstruction (M : Matching P 4) (weight : Label → ℂ)
    (labels : Label → Fin 4 → Label) (hfirst : ∀ a, labels a 0 = a) (hw : ∀ a, weight a ≠ 0)
    (hthird : LabelVaries labels 3) (hfused : ∃ a b, labels a 1+labels a 2 ≠ labels b 1+labels b 2) :
    ¬ PairSafe (tensor M weight labels) := by
  intro hs
  let i₀ := survivorIndex 0 (by decide)
  let i₁ := survivorIndex 1 (by decide)
  let i₃ := survivorIndex 3 (by decide)
  have h01 : i₀ ≠ i₁ := fun h => (by decide : (0 : Fin 4) ≠ 1) (survivorIndex_injective _ _ _ _ h)
  have h03 : i₀ ≠ i₃ := fun h => (by decide : (0 : Fin 4) ≠ 3) (survivorIndex_injective _ _ _ _ h)
  have h13 : i₁ ≠ i₃ := fun h => (by decide : (1 : Fin 4) ≠ 3) (survivorIndex_injective _ _ _ _ h)
  have hlabel (a : Label) : fusedLabels 1 2 0 labels a i₀ = a := by
    rw [fused_at_survivor]
    exact hfirst a
  have hv₀ : LabelVaries (fusedLabels 1 2 0 labels) i₀ := by
    refine ⟨0,xLabel,?_⟩
    rw [hlabel,hlabel]
    decide
  have hv₁ : LabelVaries (fusedLabels 1 2 0 labels) i₁ := by
    obtain ⟨a,b,h⟩ := hfused
    refine ⟨a,b,?_⟩
    simpa only [i₁,fused_at_survivor,ite_true] using h
  have hv₃ : LabelVaries (fusedLabels 1 2 0 labels) i₃ := by
    obtain ⟨a,b,h⟩ := hthird
    refine ⟨a,b,?_⟩
    simpa only [i₃,fused_at_survivor,show (3 : Fin 4) ≠ 1 by decide,ite_false] using h
  have hwn (a : Label) : fusedWeight weight labels 1 2 0 a ≠ 0 :=
    fun h => hw a ((fusedWeight_zero_iff weight labels 1 2 0 a).mp h)
  have hnot := three_variable_edges_not_safe (fusedMatching M 1 2)
    (fusedWeight weight labels 1 2 0) (fusedLabels 1 2 0 labels) i₀ hlabel hwn
    i₀ i₁ i₃ h01 h03 h13 hv₀ hv₁ hv₃
  apply hnot
  have huv : M.ports (1,true) ≠ M.ports (2,false) := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 2) (congrArg Prod.fst (M.ports.injective h))
  have hh := hs _ _ huv 0
  rwa [contract_cross_fiber M weight labels 1 2 (by decide) 0] at hh

theorem permutation_varies (p : Equiv.Perm Label) : ∃ a b, p a ≠ p b := by
  refine ⟨p.symm 0,p.symm xLabel,?_⟩
  simp only [Equiv.apply_symm_apply]
  decide

/-- The full permutation-fiber form is impossible with all proper exotic
cards safe. A card violating safety is derived rather than assumed. -/
theorem permutation_fiber_obstruction (M : Matching P 4) (weight : Label → ℂ)
    (perms : Fin 4 → Equiv.Perm Label) (hfirst : ∀ a, perms 0 a = a) (hw : ∀ a, weight a ≠ 0) :
    ¬ PairSafe (tensor M weight (fun a e => perms e a)) := by
  let labels : Label → Fin 4 → Label := fun a e => perms e a
  rcases one_fused_map_varies (perms 1) (perms 2) with h | h
  · exact fused_variation_obstruction M weight labels hfirst hw (permutation_varies (perms 3)) h
  · intro hs
    have he := reverse_fiber M weight labels 1
    have hs' : PairSafe (tensor (reversedMatching M 1) (reversedWeight weight labels 1)
        (reversedLabels labels 1)) := by rw [←he]; exact hs
    apply fused_variation_obstruction (reversedMatching M 1) (reversedWeight weight labels 1)
      (reversedLabels labels 1) _ (reversedWeight_nonzero weight labels 1 hw) _ _ hs'
    · intro a
      simpa only [reversedLabels,show (0 : Fin 4) ≠ 1 by decide,ite_false] using hfirst a
    · obtain ⟨a,b,hab⟩ := permutation_varies (perms 3)
      refine ⟨a,b,?_⟩
      simpa only [reversedLabels,show (3 : Fin 4) ≠ 1 by decide,ite_false] using hab
    · obtain ⟨a,b,hab⟩ := h
      refine ⟨a,b,?_⟩
      simpa only [reversedLabels,ite_true,show (2 : Fin 4) ≠ 1 by decide,ite_false] using hab

end Fiber
end
end Holant.Pauli.ExoticKlein
