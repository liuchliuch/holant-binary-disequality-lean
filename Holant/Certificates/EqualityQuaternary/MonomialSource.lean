import Holant.Certificates.EqualityQuaternary.Primality

/-! Source A.7/A.8, complete monomial-dihedral row.  The original tensor is
assumed prime across every nonempty port partition.  The conclusion supplies
an exact ordinary network containing one original q and only literal I
vertices otherwise, and actual realization over the original family.
This module does not claim the C2 or either Klein row.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Holant.EightVertex.ProductAnchor (EndpointEven)

theorem parity_weight (x : Word) : parity x = true ↔ Holant.weight x % 2 = 1 := by
  simp only [Holant.weight,Fin.sum_univ_succ]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [parity,h0,h1,h2,h3]

theorem monomial_endpoint_flip {F : SignatureFamily Scalar} {m : ℕ} (hm : 3 ≤ m)
    (reps : MonomialRepresentatives F m) (q : Signature Scalar 4) (hq : q ≠ 0)
    (hdeck : MonomialPhysicalDeck reps q) :
    ∃ mask : Word, EndpointEven (Flip.value q mask) := by
  obtain ⟨mask,hmask⟩ : ∃ mask, q mask ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hq (funext hh)
  have hds := deckSupport_of_samples hm 1 one_ne_zero (by simp)
    (complexTensor q) (monomial_safeDeck hm reps q hdeck)
  have hbit (x : Word) : nonzeroBit (complexTensor q x) = true ↔ q x ≠ 0 := by
    simp [complexTensor]
  have hc : q (complement mask) ≠ 0 :=
    (hbit _).mp (complement_of_nonzero hds ((hbit _).mpr hmask))
  refine ⟨mask,?_,?_,?_⟩
  · simpa [Flip.value,xorWord] using hmask
  · simpa [Flip.value,xorWord,complement] using hc
  · intro x hx
    by_contra hn
    have hp := parity_eq hds ((hbit _).mpr hn) ((hbit _).mpr hmask)
    change parity (xorWord x mask) = parity mask at hp
    rw [parity_xorWord,(parity_weight x).mpr hx] at hp
    cases hs : parity mask <;> simp [hs] at hp

theorem Flip.quaternary_count (q : Signature Scalar 4) (mask : Word) :
    (Finset.univ.filter (fun v : Fin (Flip.network q mask).shape.vertices =>
      (Flip.network q mask).shape.arity v = 4)).card = 1 := by
  classical
  have he : Finset.univ.filter (fun v : Fin (Flip.network q mask).shape.vertices =>
      (Flip.network q mask).shape.arity v = 4) = {Flip.ancestor q mask} := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hv
      by_contra hn
      have hh := congrArg Sigma.fst ((Flip.labels_exact q mask).2 v hn)
      simp only at hh
      omega
    · rintro rfl
      exact congrArg Sigma.fst (Flip.labels_exact q mask).1
  rw [he,Finset.card_singleton]

/-- Monomial-dihedral row of the physical equality-accessible quaternary
certificate.  The bound counts original q vertices in the displayed actual
native-X network, and is stronger than the source's two-copy bound. -/
theorem source_monomial_boundary {F : SignatureFamily Scalar} {m : ℕ} (hm : 3 ≤ m)
    (reps : MonomialRepresentatives F m) (q : Signature Scalar 4)
    (hq : TensorPrime q) (hqActual : Gadget.Realizes F .disequality q)
    (hI : Gadget.Realizes F .disequality (kernelSignature Signature.equality))
    (hdeck : MonomialPhysicalDeck reps q) :
    ∃ mask : Word,
      EndpointEven (Flip.value q mask) ∧ TensorPrime (Flip.value q mask) ∧
      ¬GroupMatching (groupM m) (Flip.value q mask) ∧
      Gadget.Realizes F .disequality (Flip.value q mask) ∧
      (Flip.network q mask).denote = Flip.value q mask ∧
      (∀ e, (Flip.network q mask).edge e = Signature.disequality) ∧
      (⟨(Flip.network q mask).shape.arity (Flip.ancestor q mask),
        (Flip.network q mask).vertex (Flip.ancestor q mask)⟩ : AnySignature Scalar) = ⟨4,q⟩ ∧
      (∀ v, v ≠ Flip.ancestor q mask →
        (⟨(Flip.network q mask).shape.arity v,(Flip.network q mask).vertex v⟩ : AnySignature Scalar) =
          ⟨2,kernelSignature Signature.equality⟩) ∧
      (Finset.univ.filter (fun v : Fin (Flip.network q mask).shape.vertices =>
        (Flip.network q mask).shape.arity v = 4)).card ≤ 2 := by
  classical
  obtain ⟨mask,he⟩ := monomial_endpoint_flip hm reps q hq.1 hdeck
  have hp := flip_prime hq mask
  exact ⟨mask,he,hp,prime_not_matching hp,Flip.actual F q hqActual hI mask,
    Flip.denote q mask,Flip.native q mask,(Flip.labels_exact q mask).1,
    (Flip.labels_exact q mask).2,by rw [Flip.quaternary_count]; omega⟩

end Holant.Certificates.EqualityQuaternary
