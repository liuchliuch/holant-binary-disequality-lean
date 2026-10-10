import Holant.Pauli.ExoticKlein.EightPortContractions
import Holant.Pauli.ExoticKlein.EightPortLabels
import Holant.Pauli.ExoticKlein.EightPortSupport
import Holant.Tensor
import Mathlib.LinearAlgebra.Basis.Defs

/-! Theorem A.14 for the stipulated actual eight-port normal form. Only the
two specified literal pair contractions are needed to contradict safe cards. -/
namespace Holant.Pauli.ExoticKlein.EightPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Zero cards are retained. A nonzero safe card is a literal scalar multiple
of three exotic binaries on an actual oriented perfect matching. -/
def SafeMatching {P : Type*} (h : Tensor ℂ P) : Prop :=
  h = 0 ∨ ∃ M : Matching P 3, ∃ labels : Fin 3 → Label, ∃ s : ℂ,
    s ≠ 0 ∧ h = fun x => s*M.tensor labels x

/-- All 28 original unordered port pairs and all four actual exotic duals. -/
def AllSafeCards (h : Signature ℂ 8) : Prop :=
  ∀ r s : Fin 8, r < s → ∀ a : Label, SafeMatching (pairCard r s a h)

abbrev CardContext := {p : Fin 8 × Fin 8 // p.1 < p.2} × Label

theorem card_context_count : Fintype.card CardContext = 112 := by
  have hp : Fintype.card {p : Fin 8 × Fin 8 // p.1 < p.2} = 28 := by decide
  rw [Fintype.card_prod,hp,card_label]

/-- A genuine factorization over a nontrivial partition of the original ports.
Both factor arities are positive, both tensors nonzero, and the exact tensor
product is transported by an explicit port bijection. -/
def HasProperTensorFactor (h : Signature ℂ 8) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ ports : (Fin m ⊕ Fin n) ≃ Fin 8,
    ∃ f : Signature ℂ m, ∃ g : Signature ℂ n,
      f ≠ 0 ∧ g ≠ 0 ∧ h = Tensor.reindex ports (Tensor.tensor f g)

 theorem fourTensor_not_safe {P : Type*} [Fintype P] [LinearOrder P]
    (M : Matching P 3) (weight : Label → ℂ) (labels : Label → Fin 3 → Label)
    (hfirst : ∀ g, labels g 0 = g) (hw : ∀ g, weight g ≠ 0)
    (hvar : ∀ i, ∃ a b, labels a i ≠ labels b i) :
    ¬SafeMatching (fourTensor M weight labels) := by
  rintro (hz | ⟨N,fixed,s,hs,he⟩)
  · exact fourTensor_ne_zero M weight labels hfirst hw hz
  · exact fourTensor_not_matching M weight labels hfirst hw hvar N fixed s hs he

/-- The actual normal form cannot have both of these two specified safe cards.
The middle label map is proved nonzero for at least one of the two port orders. -/
theorem two_cards_not_both_safe (lambda : Label → ℂ) (A1 A2 A3 : Label ≃+ Label)
    (hlambda : ∀ g, lambda g ≠ 0) :
    ¬(SafeMatching (pairCard 2 4 0 (normalForm lambda A1 A2 A3)) ∧
      SafeMatching (pairCard 3 4 0 (normalForm lambda A1 A2 A3))) := by
  rintro ⟨h35,h45⟩
  rcases D35_or_D45_nonzero A1 A2 with hD | hD
  · rw [pairCard35_normalForm] at h35
    exact fourTensor_not_safe residual35 (weight35 lambda A1 A2) (labelTriple (D35 A1 A2) A3)
      (labelTriple_first _ _) (weight35_ne_zero lambda A1 A2 hlambda)
      (labelTriple_all_vary _ (D35_zero A1 A2) hD A3) h35
  · rw [pairCard45_normalForm] at h45
    exact fourTensor_not_safe residual45 (weight45 lambda A1 A2) (labelTriple (D45 A1 A2) A3)
      (labelTriple_first _ _) (weight45_ne_zero lambda A1 A2 hlambda)
      (labelTriple_all_vary _ (D45_zero A1 A2) hD A3) h45

 theorem normalForm_not_all_safe (lambda : Label → ℂ) (A1 A2 A3 : Label ≃+ Label)
    (hlambda : ∀ g, lambda g ≠ 0) : ¬AllSafeCards (normalForm lambda A1 A2 A3) := by
  intro hs
  exact two_cards_not_both_safe lambda A1 A2 A3 hlambda
    ⟨hs 2 4 (by decide) 0,hs 3 4 (by decide) 0⟩

/-- Theorem A.14, with actual normal form, actual cards, and genuine proper
factor conclusion. Its hypotheses imply the stronger contradiction above. -/
theorem eight_port_has_proper_tensor_factor (h : Signature ℂ 8)
    (lambda : Label → ℂ) (A1 A2 A3 : Label ≃+ Label)
    (hnormal : h = normalForm lambda A1 A2 A3) (hlambda : ∀ g, lambda g ≠ 0)
    (hsafe : AllSafeCards h) : HasProperTensorFactor h := by
  exact False.elim (normalForm_not_all_safe lambda A1 A2 A3 hlambda (hnormal ▸ hsafe))

/-- The same statement with the manuscript's explicit invertible F₂-linear
maps; only their actual additive equivalences are needed by the proof. -/
theorem eight_port_linear_has_proper_tensor_factor (h : Signature ℂ 8)
    (lambda : Label → ℂ) (A1 A2 A3 : Label ≃ₗ[ZMod 2] Label)
    (hnormal : h = normalForm lambda A1.toAddEquiv A2.toAddEquiv A3.toAddEquiv)
    (hlambda : ∀ g, lambda g ≠ 0) (hsafe : AllSafeCards h) : HasProperTensorFactor h :=
  eight_port_has_proper_tensor_factor h lambda A1.toAddEquiv A2.toAddEquiv A3.toAddEquiv hnormal hlambda hsafe

end
end Holant.Pauli.ExoticKlein.EightPort
