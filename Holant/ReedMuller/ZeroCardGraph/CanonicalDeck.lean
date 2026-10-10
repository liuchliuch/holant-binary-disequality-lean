import Holant.ReedMuller.ZeroCardGraph.Source
import Holant.Dihedral.CompatibleCoefficientLine.PortAlignment

/-! All residual reorderings follow from the actual canonical ordered-pair
deck. The binary representative and its scale are unchanged. -/
noncomputable section
namespace Holant.ReedMuller.ZeroCardGraph
open Holant Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Certificates.MatchingContractionClosure
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

 def selectedPair_ne (o : Equiv.Perm (Fin (n+2))) : o 0≠o 1 :=
  fun h => Fin.zero_ne_one (o.injective h)

 def permutationRemaining (o : Equiv.Perm (Fin (n+2))) : Fin n ≃ ZeroCardGraph.Remaining (o 0) (o 1) :=
  Equiv.ofBijective (fun k => ⟨o k.succ.succ,by
    constructor
    · intro h
      exact Fin.succ_ne_zero k.succ (o.injective h)
    · intro h
      exact Fin.succ_succ_ne_one k (o.injective h)⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j h
      have he := o.injective (congrArg Subtype.val h)
      exact Fin.succ_inj.mp (Fin.succ_inj.mp he),by
      have hh := remaining_card_add_two (o 0) (o 1) (selectedPair_ne o)
      simp only [Fintype.card_fin] at hh ⊢
      omega⟩)

 def canonicalResidual (o : Equiv.Perm (Fin (n+2))) : Equiv.Perm (Fin n) :=
  (permutationRemaining o).trans (residualOrder (o 0) (o 1) (selectedPair_ne o)).symm

 theorem canonical_order_decomposition (o : Equiv.Perm (Fin (n+2))) :
    o=(liftPair (canonicalResidual o)).trans (pairOrder (o 0) (o 1)) := by
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · exact (pairOrder_first _ _ (selectedPair_ne o)).symm
  · exact (pairOrder_second _ _).symm
  · change o k.succ.succ=(residualOrder (o 0) (o 1) (selectedPair_ne o)
      ((residualOrder (o 0) (o 1) (selectedPair_ne o)).symm (permutationRemaining o k))).val
    rw [Equiv.apply_symm_apply]
    rfl

 theorem contract_residual_reindex {K : Type*} [CommSemiring K] (C : Kernel K)
    (q : Signature K (n+2)) (r : Equiv.Perm (Fin n)) :
    Signature.contract C (Tensor.reindex (liftPair r).symm q)=
      Tensor.reindex r.symm (Signature.contract C q) := by
  funext x
  simp only [Signature.contract,Tensor.reindex]
  simp_rw [word_liftPair]

 theorem representativeCard_canonical (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (o : Equiv.Perm (Fin (n+2))) (minus : Bool) :
    representativeCard R f o minus = Tensor.reindex (canonicalResidual o).symm
      (representativeCard R f (pairOrder (o 0) (o 1)) minus) := by
  unfold representativeCard
  conv_lhs => rw [canonical_order_decomposition o]
  rw [Equiv.symm_trans,←Tensor.reindex_trans,contract_residual_reindex]

 def CanonicalMatchingDeck (G : Set (Binary (K := ℂ))) (R : FixedIXRepresentatives)
    (f : Signature ℂ (n+2)) : Prop :=
  ∀i j : Fin (n+2),i≠j → ∀ minus : Bool,MatchingOrZero G (representativeCard R f (pairOrder i j) minus)

 theorem actualMatchingDeck_of_canonical {G : Set (Binary (K := ℂ))}
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (h : CanonicalMatchingDeck G R f) : ActualMatchingDeck G R f := by
  intro o minus
  rw [representativeCard_canonical]
  exact (h (o 0) (o 1) (selectedPair_ne o) minus).reindex _

 theorem source_canonical_zero_card_graph {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2)) (hf : f≠0)
    (hn : 4<n+2) (hdeck : CanonicalMatchingDeck G R f) : graph (CoefficientAtlas.walsh f)=⊥ :=
  source_zero_card_graph hG hspan R f hf hn (actualMatchingDeck_of_canonical R f hdeck)

end Holant.ReedMuller.ZeroCardGraph
