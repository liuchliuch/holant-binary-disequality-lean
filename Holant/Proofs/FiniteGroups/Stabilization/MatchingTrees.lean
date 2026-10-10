import Holant.Proofs.FiniteGroups.Stabilization.BinaryPrimes
import Holant.Certificates.MatchingContractionClosure.Presentation
import Mathlib.Logic.Equiv.Prod


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L P Q : Type*} [Field L]

def singleBinaryPresentation (B : Binary (K := L)) : Presentation L (Fin 2) where
  edges := 1
  ports := (Equiv.uniqueProd Bool (Fin 1)).trans finTwoEquiv.symm
  matrix := fun _ => B
  scalar := 1

theorem singleBinaryPresentation_tensor (B : Binary (K := L)) :
    (singleBinaryPresentation B).tensor = binarySignature B := by
  funext x
  simp [singleBinaryPresentation, Presentation.tensor, productValue, binarySignature,
    Equiv.uniqueProd, finTwoEquiv]

def joinPresentations (M : Presentation L P) (N : Presentation L Q) (c : L) :
    Presentation L (P ⊕ Q) :=
  Presentation.ofFinite
    ((Equiv.sumProdDistrib (Fin M.edges) (Fin N.edges) Bool).trans (Equiv.sumCongr M.ports N.ports))
    (Sum.elim M.matrix N.matrix) (c * M.scalar * N.scalar)

theorem joinPresentations_tensor (M : Presentation L P) (N : Presentation L Q) (c : L) :
    (joinPresentations M N c).tensor = c • Tensor.tensor M.tensor N.tensor := by
  classical
  rw [joinPresentations, Presentation.ofFinite_tensor]
  funext x
  simp only [productValue, Fintype.prod_sum_type, Equiv.trans_apply,
    Equiv.sumProdDistrib_apply_left, Equiv.sumProdDistrib_apply_right,
    Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Pi.smul_apply, smul_eq_mul, Tensor.tensor_apply, Presentation.tensor]
  ring

theorem joinPresentations_valid {S : Set (Binary (K := L))}
    (M : Presentation L P) (N : Presentation L Q) (c : L)
    (hM : M.Valid S) (hN : N.Valid S) : (joinPresentations M N c).Valid S := by
  apply Presentation.ofFinite_valid
  intro i
  cases i with
  | inl i => exact hM i
  | inr i => exact hN i

theorem FactorTree.matching_presentation {f : AnySignature L} (t : FactorTree f)
    (F : SignatureFamily L)
    (hret : ∀ a ∈ t.leaves, a ∈ F) (hbin : ∀ a ∈ t.leaves, a.1 = 2) :
    ∃ M : Presentation L (Fin f.1), M.Valid (actualTransfers F) ∧ M.scalar ≠ 0 ∧ f.2 = M.tensor := by
  classical
  revert hret hbin
  induction t with
  | leaf f hp =>
      intro hret hbin
      have hf := hret f (by simp [FactorTree.leaves])
      have hn := hbin f (by simp [FactorTree.leaves])
      rcases f with ⟨n, f⟩
      dsimp only at hn
      subst n
      refine ⟨singleBinaryPresentation (binaryMatrix f), ?_, one_ne_zero, ?_⟩
      · intro i
        exact retained_binary_prime_safe F f hf hp
      · rw [singleBinaryPresentation_tensor, binarySignature_binaryMatrix]
  | split s ta tb iha ihb =>
      intro hret hbin
      obtain ⟨M, hM, hm, heM⟩ := iha
        (fun a ha => hret a (Multiset.mem_add.mpr (Or.inl ha)))
        (fun a ha => hbin a (Multiset.mem_add.mpr (Or.inl ha)))
      obtain ⟨N, hN, hn, heN⟩ := ihb
        (fun a ha => hret a (Multiset.mem_add.mpr (Or.inr ha)))
        (fun a ha => hbin a (Multiset.mem_add.mpr (Or.inr ha)))
      refine ⟨(joinPresentations M N (s.scale : L)).reindex s.ports,
        joinPresentations_valid M N (s.scale : L) hM hN,
        mul_ne_zero (mul_ne_zero s.scale.ne_zero hm) hn, ?_⟩
      rw [Presentation.reindex_tensor, joinPresentations_tensor, s.equation, heM, heN]
      rfl

theorem FactorTree.matchingOrZero {f : AnySignature L} (t : FactorTree f)
    (F : SignatureFamily L) (hret : ∀ a ∈ t.leaves, a ∈ F)
    (hbin : ∀ a ∈ t.leaves, a.1 = 2) : MatchingOrZero (actualTransfers F) f.2 :=
  Or.inr (t.matching_presentation F hret hbin)

/-- Retention preserves a proved matching presentation, even if the actual
complete group subsequently grows.  This does not assert that a new deck is
automatically stable after such growth. -/
theorem matchingOrZero_retained {F G : SignatureFamily L} (hFG : F ⊆ G)
    {n : ℕ} {f : Signature L n} (hf : MatchingOrZero (actualTransfers F) f) :
    MatchingOrZero (actualTransfers G) f := by
  rcases hf with hz | ⟨M, hM, hc, he⟩
  · exact Or.inl hz
  · exact Or.inr ⟨M, fun i => actualTransfers_mono hFG (hM i), hc, he⟩

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
