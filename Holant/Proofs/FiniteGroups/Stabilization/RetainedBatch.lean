import Holant.Proofs.FiniteGroups.Stabilization.MinimumCore
import Holant.Proofs.FiniteGroups.Stabilization.FrozenWorklist


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

noncomputable section
variable {L κ : Type*} [Field L] [DecidableEq κ]

/-- Chosen exact prime decompositions stay inside the family.  The definition
does not require closure under arbitrary scalar representatives of factors. -/
def FactorSaturated (F : SignatureFamily L) : Prop :=
  ∀ f ∈ F, f.2 ≠ 0 → ∃ t : FactorTree f, ∀ a ∈ t.leaves, a ∈ F

def batchCarrier (U : Finset κ) (root : κ → TreeOccurrence L) : Finset (AnySignature L) := by
  classical
  exact U.biUnion (fun k => insert (root k).1 (root k).2.leaves.toFinset)

theorem mem_batchCarrier (U : Finset κ) (root : κ → TreeOccurrence L)
    (f : AnySignature L) :
    f ∈ batchCarrier U root ↔ ∃ k ∈ U, f = (root k).1 ∨ f ∈ (root k).2.leaves := by
  classical
  simp [batchCarrier]

def retainBatch (F : SignatureFamily L) (U : Finset κ) (root : κ → TreeOccurrence L) :
    SignatureFamily L := F ∪ (batchCarrier U root : Set (AnySignature L))

theorem retainBatch_retains (F : SignatureFamily L) (U : Finset κ)
    (root : κ → TreeOccurrence L) : F ⊆ retainBatch F U root := fun _ hf => Or.inl hf

theorem retainBatch_finite {F : SignatureFamily L} (hF : F.Finite)
    (U : Finset κ) (root : κ → TreeOccurrence L) : (retainBatch F U root).Finite :=
  hF.union (batchCarrier U root).finite_toSet

theorem retainBatch_root (F : SignatureFamily L) (U : Finset κ)
    (root : κ → TreeOccurrence L) {k : κ} (hk : k ∈ U) : (root k).1 ∈ retainBatch F U root :=
  Or.inr ((mem_batchCarrier U root _).mpr ⟨k, hk, Or.inl rfl⟩)

theorem retainBatch_leaf (F : SignatureFamily L) (U : Finset κ)
    (root : κ → TreeOccurrence L) {k : κ} (hk : k ∈ U)
    {a : AnySignature L} (ha : a ∈ (root k).2.leaves) : a ∈ retainBatch F U root :=
  Or.inr ((mem_batchCarrier U root _).mpr ⟨k, hk, Or.inr ha⟩)

/-- The new leaves are actually prime, so their singleton decompositions
close the saturation proof without another factorization oracle. -/
theorem retainBatch_saturated {F : SignatureFamily L} (hF : FactorSaturated F)
    (U : Finset κ) (root : κ → TreeOccurrence L) : FactorSaturated (retainBatch F U root) := by
  intro f hf hn
  rcases hf with hf | hf
  · obtain ⟨t, ht⟩ := hF f hf hn
    exact ⟨t, fun a ha => Or.inl (ht a ha)⟩
  · obtain ⟨k, hk, he | hl⟩ := (mem_batchCarrier U root f).mp hf
    · subst f
      exact ⟨(root k).2, fun a ha => retainBatch_leaf F U root hk ha⟩
    · refine ⟨.leaf f ((root k).2.leaves_prime f hl), ?_⟩
      intro a ha
      have he : a = f := by simpa only [FactorTree.leaves, Multiset.mem_singleton] using ha
      subst a
      exact retainBatch_leaf F U root hk hl

/-- Finite mathematical saturation is available for any finite nonzero
family by choosing finite trees.  No effective factor-access claim follows. -/
theorem exists_finite_saturation (F : SignatureFamily L) (hF : F.Finite)
    (hn : ∀ f ∈ F, f.2 ≠ 0) :
    ∃ G : SignatureFamily L, G.Finite ∧ F ⊆ G ∧ FactorSaturated G := by
  classical
  let root : F → TreeOccurrence L := fun f => ⟨f.1, (exists_factorTree f.1 (hn f.1 f.2)).some⟩
  letI : Fintype F := hF.fintype
  let G := retainBatch (∅ : SignatureFamily L) Finset.univ root
  refine ⟨G, retainBatch_finite Set.finite_empty _ _, ?_, ?_⟩
  · intro f hf
    exact retainBatch_root ∅ Finset.univ root (k := ⟨f, hf⟩) (Finset.mem_univ _)
  · exact retainBatch_saturated (fun f hf _ => False.elim hf) _ _

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
