import Holant.ReedMuller.MatchingConsistency.GlobalEquality
import Holant.ReedMuller.ZeroCardGraph.CanonicalDeck

/-! Source Lemma 7.7 from the literal fixed-representative canonical I/X
deck. The matching and matching agreement are conclusions. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.CoefficientAtlas
open Holant.Certificates.MatchingContractionClosure
variable {ι K : Type*} [DecidableEq ι] [Field K]

/-- The four clauses of matching consistency, in original named ports. -/
structure Consistent (f : Tensor K ι) : Prop where
  constant_ne_zero : f (fun _=>false)≠0
  weight_matching : ∀u v w,(weightGraph f).Adj u v → (weightGraph f).Adj u w → v=w
  card_matchings_agree : ∀ i j : ι,i≠j → ∀ P Q : Pairing (ZeroCardGraph.Remaining i j),
    (∀x,card f i j false x≠0 ↔ P.Support x) →
    (∀x,card f i j true x≠0 ↔ Q.Support x) → P.mate=Q.mate
  global_equality : ∀p q : ι,(weightGraph f).Adj p q → ∀x,f x≠0 → x p=x q

 theorem equality_deck_consistent [Fintype ι] (htwo : (2:K)≠0) (f : Tensor K ι)
    (hn : 6≤Fintype.card ι) (hdeck : EqualityDeck f) (hzero : graph f=⊥) : Consistent f where
  constant_ne_zero := hdeck.constant_ne_zero htwo hn hzero
  weight_matching := hdeck.weight_matching htwo hn
  card_matchings_agree := hdeck.card_matchings_agree htwo hn
  global_equality := hdeck.global_equality htwo hn

/-- Literal source hypothesis, using only original ordered deleted pairs.
Every residual permutation is proved from actual tensor reindexing. The
zero-graph premise is itself derived by source 7.6. -/
 theorem source_matching_consistency {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    (R : FixedIXRepresentatives) (f : Signature ℂ (n+2)) (hf : f≠0)
    (hn : 6≤n+2) (hdeck : CanonicalMatchingDeck G R f) : Consistent (walsh f) := by
  have ha := actualMatchingDeck_of_canonical R f hdeck
  exact equality_deck_consistent (by norm_num) (walsh f) (by simpa using hn)
    (actual_equality_deck hG hspan R f ha)
    (source_zero_card_graph hG hspan R f hf (by omega) ha)

end Holant.ReedMuller.MatchingConsistency
