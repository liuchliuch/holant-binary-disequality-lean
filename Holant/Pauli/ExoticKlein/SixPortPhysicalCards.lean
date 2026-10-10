import Holant.Pauli.ExoticKlein.SixPortMatchingLines
import Holant.Pauli.ExoticKlein.SixPortModel

/-! Equivalence between the checker-facing ordered card condition and the
actual original-port condition with arbitrary oriented matching products. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
open ProjectiveDetermination

 def OnMatching {P : Type*} (h : Tensor ℂ P) : Prop :=
  h = 0 ∨ ∃ M : Matching P 2, ∃ labels : Fin 2 → Label, ∃ s : ℂ,
    s ≠ 0 ∧ h = fun x => s*M.tensor labels x

 theorem onMatching_reindex {P R : Type*} (e : P ≃ R) (h : Tensor ℂ P) (hh : OnMatching h) :
    OnMatching (Tensor.reindex e h) := by
  rcases hh with rfl | ⟨M,labels,s,hs,rfl⟩
  · left; rfl
  · right
    refine ⟨⟨M.ports.trans e⟩,labels,s,hs,?_⟩
    rfl

 theorem onMatching_reindex_iff {P R : Type*} (e : P ≃ R) (h : Tensor ℂ P) :
    OnMatching (Tensor.reindex e h) ↔ OnMatching h := by
  constructor
  · intro hh
    have h' := onMatching_reindex e.symm (Tensor.reindex e h) hh
    have he : Tensor.reindex e.symm (Tensor.reindex e h) = h := by
      funext x
      simp only [Tensor.reindex,Equiv.symm_apply_apply]
    rwa [he] at h'
  · exact onMatching_reindex e h

 def physicalCard (r s : Fin 6) (a : Label) (h : Signature ℂ 6) : Tensor ℂ (Rest r s) :=
  fun z => ∑ u : Bool, ∑ v : Bool, dual a u v*h (fill r s u v z)

 theorem card_as_physical_reindex (p : Fin 15) (a : Label) (h : Signature ℂ 6) :
    card p a h = Tensor.reindex (remainingEquiv p).symm
      (physicalCard (portPairs p).val.1 (portPairs p).val.2 a h) := rfl

 theorem card_onDirection_iff_physical (p : Fin 15) (a : Label) (h : Signature ℂ 6) :
    OnDirection (card p a h) ↔ OnMatching (physicalCard (portPairs p).val.1 (portPairs p).val.2 a h) := by
  rw [onDirection_iff_matching]
  change OnMatching (card p a h) ↔ _
  rw [card_as_physical_reindex,onMatching_reindex_iff]

/-- This is the manuscript hypothesis: every actual exotic pair card on the
original six ports is zero or a scaled product of two exotic binaries. -/
 def AllPhysicalSafe (h : Signature ℂ 6) : Prop :=
  ∀ r s : Fin 6, r < s → ∀ a : Label, OnMatching (physicalCard r s a h)

 theorem allPhysicalSafe_iff_ordered (h : Signature ℂ 6) : AllPhysicalSafe h ↔ SafeOrderedCards h := by
  constructor
  · intro hs p a
    exact (card_onDirection_iff_physical p a h).mpr
      (hs _ _ (portPairs p).property a)
  · intro hs r s hrs a
    obtain ⟨p,hp⟩ := portPairs_bijective.surjective ⟨(r,s),hrs⟩
    have hh := (card_onDirection_iff_physical p a h).mp (hs p a)
    have he := congrArg Subtype.val hp
    have hr := congrArg Prod.fst he
    have hss := congrArg Prod.snd he
    rwa [hr,hss] at hh

 theorem normalized_product_of_checked_physical (state : DirectionTriple)
    (certificate : LinearCertificate.Certificate 4 64 60 48 960)
    (hc : certificate.check (problem state) (initialRows state) = true)
    (scale : Fin 4 → ℂ) (ha : Admissible state scale)
    (hs : AllPhysicalSafe (normalizedTensor state scale)) (hn : normalizedTensor state scale ≠ 0) :
    IsProduct (normalizedTensor state scale) :=
  normalized_product_of_checked state certificate hc scale ha (allPhysicalSafe_iff_ordered _ |>.mp hs) hn

end
end Holant.Pauli.ExoticKlein.SixPort
