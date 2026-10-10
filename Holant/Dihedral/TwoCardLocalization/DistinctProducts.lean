import Holant.Dihedral.TwoCardLocalization.ResidualOrder
import Holant.Pauli.ExoticKlein.RulingCrossSemantics

/-! Generic reduction of two distinct matching products to four residual ports.
Every chosen pair crosses two edges in BOTH products, so one fixed nonsingular
kernel suffices and no simultaneous trace or label agreement is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Certificates Holant.Pauli.ExoticKlein
open Holant.Dihedral.CompatibleClosure
variable {K : Type*} [Field K]

abbrev presentationMatching {P : Type*} (M : MatchingContractionClosure.Presentation K P) : Matching P M.edges :=
  ⟨M.ports⟩

def DifferentProducts (G : Set (Kernel K)) (n : ℕ) (q₀ q₁ : Signature K n) : Prop :=
  ∃ M₀ M₁ : MatchingContractionClosure.Presentation K (Fin n),
    M₀.Valid G ∧ M₁.Valid G ∧ M₀.scalar ≠ 0 ∧ M₁.scalar ≠ 0 ∧
    q₀=M₀.tensor ∧ q₁=M₁.tensor ∧ (presentationMatching M₀).mate ≠ (presentationMatching M₁).mate

theorem presentationMatching_reindex {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (M : MatchingContractionClosure.Presentation K P) (e : P ≃ Q) (u : P) :
    (presentationMatching (M.reindex e)).mate (e u)=e ((presentationMatching M).mate u) := by
  simp [presentationMatching,MatchingContractionClosure.Presentation.reindex,Matching.mate]

theorem different_reindex {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (M₀ M₁ : MatchingContractionClosure.Presentation K P) (e : P ≃ Q)
    (h : (presentationMatching M₀).mate ≠ (presentationMatching M₁).mate) :
    (presentationMatching (M₀.reindex e)).mate ≠ (presentationMatching (M₁.reindex e)).mate := by
  intro he
  apply h
  apply Equiv.ext
  intro u
  have hh := congrArg (fun k : Equiv.Perm Q => k (e u)) he
  rw [presentationMatching_reindex,presentationMatching_reindex] at hh
  exact e.injective hh

/-- An actual smaller pair of full matching products, with the original
surviving-port surgery and ordered contraction identified exactly. -/
theorem different_products_step (G : Set (Kernel K))
    (hG : MatchingContractionClosure.ProjectiveMatrixGroup G)
    (hX : (MatchingContractionClosure.X : Kernel K) ∈ G)
    (hrev : MatchingContractionClosure.ReversalStable G)
    (C : Kernel K) (hC : MatchingContractionClosure.SafeBinary G C)
    (r : ℕ) (q₀ q₁ : Signature K (2*(r+1)+4)) (h : DifferentProducts G _ q₀ q₁) :
    ∃ p : Equiv.Perm (Fin (2*(r+1)+4)),
      DifferentProducts G (2*r+4) (Signature.contract C (Tensor.reindex p.symm q₀))
        (Signature.contract C (Tensor.reindex p.symm q₁)) := by
  obtain ⟨M₀,M₁,hM₀,hM₁,hκ₀,hκ₁,rfl,rfl,hne⟩ := h
  let m₀ := presentationMatching M₀
  let m₁ := presentationMatching M₁
  obtain ⟨u,v,huv,hu,hv,hd⟩ := MatchingSurgery.actual_disagreement_reduction m₀ m₁ hne
    (by simp only [Fintype.card_fin]; omega)
  let R₀ := MatchingSurgery.crossPresentation m₀ u v huv hu M₀.matrix M₀.scalar C
  let R₁ := MatchingSurgery.crossPresentation m₁ u v huv hv M₁.matrix M₁.scalar C
  let e := (remainingOrder u v huv).symm
  have hr₀ : R₀.Valid G := MatchingSurgery.cross_presentation_valid hG hX hrev m₀ u v huv hu _ _ C hM₀ hC
  have hr₁ : R₁.Valid G := MatchingSurgery.cross_presentation_valid hG hX hrev m₁ u v huv hv _ _ C hM₁ hC
  have he₀ : Signature.contract C (Tensor.reindex (pairOrder u v).symm M₀.tensor)=(R₀.reindex e).tensor := by
    rw [← contractPair_order u v huv C]
    have hh : MatchingContractionClosure.contractPair u v C M₀.tensor=R₀.tensor :=
      MatchingSurgery.cross_card_exact m₀ u v huv hu M₀.matrix M₀.scalar C
    exact congrArg (Tensor.reindex e) hh
  have he₁ : Signature.contract C (Tensor.reindex (pairOrder u v).symm M₁.tensor)=(R₁.reindex e).tensor := by
    rw [← contractPair_order u v huv C]
    have hh : MatchingContractionClosure.contractPair u v C M₁.tensor=R₁.tensor :=
      MatchingSurgery.cross_card_exact m₁ u v huv hv M₁.matrix M₁.scalar C
    exact congrArg (Tensor.reindex e) hh
  refine ⟨pairOrder u v,R₀.reindex e,R₁.reindex e,hr₀,hr₁,hκ₀,hκ₁,he₀,he₁,?_⟩
  apply different_reindex R₀ R₁ e
  exact hd

/-- Exactly r fixed-kernel contractions suffice for distinct original matchings
on 2r+4 residual ports. The same recorded program acts on both selected cards. -/
theorem different_products_program (G : Set (Kernel K))
    (hG : MatchingContractionClosure.ProjectiveMatrixGroup G)
    (hX : (MatchingContractionClosure.X : Kernel K) ∈ G)
    (hrev : MatchingContractionClosure.ReversalStable G)
    (C : Kernel K) (hC : MatchingContractionClosure.SafeBinary G C)
    (r : ℕ) (q₀ q₁ : Signature K (2*r+4)) (h : DifferentProducts G _ q₀ q₁) :
    ∃ P : Program Unit (2*r+4) 4, P.length=r ∧
      DifferentProducts G 4 (P.residual (fun _ => C) q₀) (P.residual (fun _ => C) q₁) := by
  apply reduce_invariant (fun _ : Unit => C) (DifferentProducts G) ?_ r q₀ q₁ h
  intro k A B hAB
  obtain ⟨p,hp⟩ := different_products_step G hG hX hrev C hC k A B hAB
  exact ⟨p,(),hp⟩

end Holant.Dihedral.TwoCardLocalization
