import Holant.ReedMuller.ZeroCardGraph.Physical
import Holant.ReedMuller.FixedCoreDeck.WalshMatchingSupport

/-! Source Lemma 7.6. The only deck premise is the literal proper-card clause
of `Stable`: each actual fixed-representative I/X card is zero or a
nonsingular G-matching. No minimality, primality, stabilization transition,
or support graph is assumed. -/
noncomputable section
namespace Holant.ReedMuller.ZeroCardGraph
open Holant Holant.ReedMuller.CoefficientAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.ReedMuller.FixedCoreDeck

/-- Actual fixed binary representatives, with their nonzero scales retained. -/
structure FixedIXRepresentatives where
  kernel : Bool → Kernel ℂ
  scale : Bool → ℂ
  scale_ne_zero : ∀ minus, scale minus ≠ 0
  exact : ∀ minus, kernel minus = scale minus •
    (if minus then Signature.disequality else Signature.equality)

variable {n : ℕ}

def representativeCard (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (o : Equiv.Perm (Fin (n+2))) (minus : Bool) : Signature ℂ n :=
  Signature.contract (R.kernel minus) (Tensor.reindex o.symm f)

theorem representativeCard_exact (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (o : Equiv.Perm (Fin (n+2))) (minus : Bool) :
    representativeCard R f o minus = R.scale minus • physicalCard f o minus := by
  funext y
  simp only [representativeCard, R.exact, physicalCard, Signature.contract,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- This is precisely the proper one-copy I/X part of the source's stabilized
minimum-core hypothesis, expressed on actual representative contractions. -/
def ActualMatchingDeck (G : Set (Binary (K := ℂ))) (R : FixedIXRepresentatives)
    (f : Signature ℂ (n+2)) : Prop :=
  ∀ o : Equiv.Perm (Fin (n+2)), ∀ minus : Bool,
    MatchingOrZero G (representativeCard R f o minus)

theorem actual_deck_nonzeroAtZero {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (hdeck : ActualMatchingDeck G R f) : NonzeroAtZeroCards (walsh f) := by
  apply nonzeroAtZero_of_physical
  intro o minus hn
  have he : walsh (representativeCard R f o minus) = R.scale minus • walsh (physicalCard f o minus) := by
    rw [representativeCard_exact,walsh_smul]
  rcases walsh_matchingOrZero_zero_value hG hspan (hdeck o minus) with hz | hz
  · apply False.elim
    apply hn
    funext y
    have hh := congrFun (he.symm.trans hz) y
    exact (mul_eq_zero.mp hh).resolve_left (R.scale_ne_zero minus)
  · intro hc
    apply hz
    rw [he]
    simp only [Pi.smul_apply,smul_eq_mul,hc,mul_zero]

/-- Every connected component is complete bipartite on the two colors of an
actual supported Walsh word; isolated vertices are included. -/
theorem source_zero_graph_components (f : Signature ℂ (n+2)) (hf : f ≠ 0) :
    ∃ w : Fin (n+2) → Bool, walsh f w ≠ 0 ∧
      ∀ root i j, (graph (walsh f)).Reachable root i → (graph (walsh f)).Reachable root j →
        ((graph (walsh f)).Adj i j ↔ w i ≠ w j) :=
  components_complete_bipartite (walsh f) (walsh_nonzero f hf)

/-- Full elimination statement from the source's actual card semantics.
It is stronger than the minimum-prime specialization: no prime or
minimality premise is needed for this local graph argument. -/
theorem source_zero_card_graph {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2)) (hf : f ≠ 0)
    (hn : 4 < n+2) (hdeck : ActualMatchingDeck G R f) : graph (walsh f) = ⊥ :=
  zero_graph_eq_bot (by norm_num) (walsh f) (walsh_nonzero f hf)
    (by simpa using hn) (actual_deck_nonzeroAtZero hG hspan R f hdeck)

/-- No original pair is invisible to both physical contractions. -/
theorem source_every_pair_visible {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2)) (hf : f ≠ 0)
    (hn : 4 < n+2) (hdeck : ActualMatchingDeck G R f)
    (i j : Fin (n+2)) (hij : i ≠ j) :
    card (walsh f) i j false ≠ 0 ∨ card (walsh f) i j true ≠ 0 :=
  every_pair_visible (by norm_num) (walsh f) (walsh_nonzero f hf)
    (by simpa using hn) (actual_deck_nonzeroAtZero hG hspan R f hdeck) i j hij

theorem walsh_eq_zero_iff {N : ℕ} (f : Signature ℂ N) : walsh f=0 ↔ f=0 := by
  constructor
  · intro h
    by_contra hf
    exact walsh_nonzero f hf h
  · rintro rfl
    exact Signature.coordinateAction_zero _

theorem representativeCard_zero_iff (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (o : Equiv.Perm (Fin (n+2))) (minus : Bool) :
    representativeCard R f o minus=0 ↔ orderedCard (walsh f) o minus=0 := by
  rw [←walsh_physical_card,walsh_eq_zero_iff,representativeCard_exact]
  constructor
  · intro h
    funext y
    exact (mul_eq_zero.mp (congrFun h y)).resolve_left (R.scale_ne_zero minus)
  · rintro h
    rw [h,smul_zero]

theorem card_zero_iff_ordered (q : Signature ℂ (n+2)) (i j : Fin (n+2)) (hij : i≠j)
    (minus : Bool) : card q i j minus=0 ↔ orderedCard q (Holant.Dihedral.CompatibleClosure.pairOrder i j) minus=0 := by
  rw [card_named_ordered q i j hij minus]
  constructor
  · intro h
    funext y
    have hh := congrFun h (fun k => y ((residualOrder i j hij).symm k))
    simpa only [Tensor.reindex,Equiv.symm_apply_apply,Pi.zero_apply] using hh
  · rintro h
    rw [h]
    rfl

/-- The graph defined from support is literally the graph of vanishing actual
fixed-representative cards on the same original ordered pair. -/
theorem graph_actual_zero_cards (R : FixedIXRepresentatives) (f : Signature ℂ (n+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    (graph (walsh f)).Adj i j ↔
      representativeCard R f (Holant.Dihedral.CompatibleClosure.pairOrder i j) false=0 ∧
      representativeCard R f (Holant.Dihedral.CompatibleClosure.pairOrder i j) true=0 := by
  rw [graph_zero_cards (by norm_num) _ _ _ hij,
    card_zero_iff_ordered _ _ _ hij,card_zero_iff_ordered _ _ _ hij,
    representativeCard_zero_iff,representativeCard_zero_iff]

 theorem source_actual_pair_visible {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2)) (hf : f ≠ 0)
    (hn : 4 < n+2) (hdeck : ActualMatchingDeck G R f)
    (i j : Fin (n+2)) (hij : i ≠ j) :
    representativeCard R f (Holant.Dihedral.CompatibleClosure.pairOrder i j) false≠0 ∨
    representativeCard R f (Holant.Dihedral.CompatibleClosure.pairOrder i j) true≠0 := by
  by_contra h
  push_neg at h
  have hh := (graph_actual_zero_cards R f i j hij).mpr h
  rw [source_zero_card_graph hG hspan R f hf hn hdeck] at hh
  exact hh

end Holant.ReedMuller.ZeroCardGraph
