import Holant.Proofs.FiniteGroups.Stabilization.FactorExposure


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L : Type*} [Field L]

def ProperSplit.composePorts {f a b c d : AnySignature L}
    (s : ProperSplit f a b) (t : ProperSplit a c d) :
    (Fin c.1 ⊕ Fin (d.1 + b.1)) ≃ Fin f.1 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans
    ((Equiv.sumAssoc (Fin c.1) (Fin d.1) (Fin b.1)).symm.trans
      ((Equiv.sumCongr t.ports (Equiv.refl _)).trans s.ports))

/-- The complementary factor is the full ordered tensor d⊗b. In
particular its nonzero scalar is not normalized away at a tree junction. -/
def ProperSplit.composeLeft {f a b c d : AnySignature L}
    (s : ProperSplit f a b) (t : ProperSplit a c d) :
    ProperSplit f c ⟨d.1 + b.1, Signature.tensor d.2 b.2⟩ where
  left_pos := t.left_pos
  right_pos := by change 0 < d.1 + b.1; have := s.right_pos; omega
  ports := s.composePorts t
  scale := s.scale * t.scale
  equation := by
    funext x
    rw [s.equation, t.equation]
    simp only [ProperSplit.composePorts, Signature.tensor_apply, Equiv.trans_apply,
      Equiv.sumCongr, Equiv.coe_fn_mk, Equiv.refl_apply, Sum.map_inl, Sum.map_inr,
      Equiv.sumAssoc_symm_apply_inl, Equiv.sumAssoc_symm_apply_inr_inl,
      Equiv.sumAssoc_symm_apply_inr_inr, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Units.val_mul]
    ring

/-- Every leaf is the root itself or has a concrete positive-arity
complement and an exact ordered split of the ORIGINAL root. -/
theorem FactorTree.leaf_split {f : AnySignature L} (t : FactorTree f)
    (g : AnySignature L) (hg : g ∈ t.leaves) :
    f = g ∨ ∃ b : AnySignature L, Nonempty (ProperSplit f g b) := by
  revert hg
  induction t with
  | leaf f hp =>
      intro hg
      left
      exact (Multiset.mem_singleton.mp hg).symm
  | @split f a b s ta tb iha ihb =>
      intro hg
      rcases Multiset.mem_add.mp hg with ha | hb
      · rcases iha ha with he | ⟨d, ⟨hd⟩⟩
        · subst g
          exact Or.inr ⟨b, ⟨s⟩⟩
        · exact Or.inr ⟨_, ⟨s.composeLeft hd⟩⟩
      · rcases ihb hb with he | ⟨d, ⟨hd⟩⟩
        · subst g
          exact Or.inr ⟨a, ⟨s.swap⟩⟩
        · exact Or.inr ⟨_, ⟨s.swap.composeLeft hd⟩⟩

/-- Root access suffices for every proper stored leaf's power exposure.
No actual-realization premise is imposed on an intermediate tree node. -/
theorem FactorTree.leaf_direct_or_power {f : AnySignature L} (t : FactorTree f)
    (g : AnySignature L) (hg : g ∈ t.leaves) (F : SignatureFamily L)
    (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (hs : GeneralCarrierExistence.MixedSupport F)
    (hf : f.2 ≠ 0) (ha : Gadget.Realizes F .disequality f.2) :
    Gadget.Realizes F .disequality g.2 ∨
      ∃ r : ℕ, 0 < r ∧ ∃ c : L, c ≠ 0 ∧ ∃ N : Network L (r * g.1),
        (∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature L) ∈ F) ∧
        (∀ e, N.edge e = Signature.disequality) ∧
        N.denote = fun x => c * Carrier.blockPower g.2 r x := by
  rcases t.leaf_split g hg with rfl | ⟨b, ⟨s⟩⟩
  · exact Or.inl ha
  · exact Or.inr (s.left_power_ordinary F hI htwo hs hf ha)

theorem fullDeckRoot_nonzero {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (i : FullDeckIndex F hτ f) :
    (fullDeckRoot F hτ f i).1.2 ≠ 0 := by
  cases i with
  | inl q => exact actualRepresentative_signature_nonzero F hτ q
  | inr k => exact k.2

/-- Every leaf of every stored raw-card or actual-representative tree has
root-to-leaf provenance over the predecessor F. Neither canonical-key
deduplication nor retention silently grants direct access to the leaf. -/
theorem fullDeck_leaf_direct_or_power {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (i : FullDeckIndex F hτ f) (g : AnySignature L)
    (hg : g ∈ (fullDeckRoot F hτ f i).2.leaves) :
    Gadget.Realizes F .disequality g.2 ∨
      ∃ r : ℕ, 0 < r ∧ ∃ c : L, c ≠ 0 ∧ ∃ N : Network L (r * g.1),
        (∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature L) ∈ F) ∧
        (∀ e, N.edge e = Signature.disequality) ∧
        N.denote = fun x => c * Carrier.blockPower g.2 r x :=
  (fullDeckRoot F hτ f i).2.leaf_direct_or_power g hg F hI htwo
    (mixedSupport_of_identity F hI)
    (fullDeckRoot_nonzero F hτ f i) (fullDeckRoot_realizes F hτ hI htwo f hf i)

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
