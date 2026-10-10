import Holant.Proofs.Closure.ContinuationCatalogue

/-! Nonminimum unchanged-group transport for any previously selected literal f.
Every current raw key keeps its ambient attachment/permutation/orientation name
and an explicit nonzero scalar in the same original field. No fresh FactorTree,
matching classification, minimum-core or common-basis hypothesis is supplied. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
open Holant Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ContinuationTransport HistoryCatalogue
variable {L : Type*} [Field L] [NumberField L]
variable (F H : SignatureFamily L) (retains : F ⊆ H)
variable (oldTorsion : ResidualTorsion F) (currentTorsion : ResidualTorsion H)
variable (sameGroup : completeGroup H currentTorsion = completeGroup F oldTorsion)
variable {m : ℕ} (f : Signature L (m+2))

/-- The actual representative change retains the complete class names. -/
def change : RepresentativeChange F oldTorsion H currentTorsion :=
  representativeChange retains oldTorsion currentTorsion sameGroup

structure Card (k : RawCardKey m (completeGroup H currentTorsion)) where
  oldKey : RawCardKey m (completeGroup F oldTorsion)
  oldKeyExact : oldKey = (change F H retains oldTorsion currentTorsion sameGroup).key k
  ambientIdentity : rawKey Subtype.val oldKey = rawKey Subtype.val k
  scalar : L
  nonzero : scalar ≠ 0
  equation : rawCard H currentTorsion f k = scalar • rawCard F oldTorsion f oldKey

/-- The scalar is constructed from actual representative/attachment transport,
not supplied as a projective-equality oracle or classification premise. -/
def card (k : RawCardKey m (completeGroup H currentTorsion)) :
    Card F H retains oldTorsion currentTorsion sameGroup f k := by
  let T := change F H retains oldTorsion currentTorsion sameGroup
  let h := rawCard_transport T f k
  let scalar := Classical.choose h
  have hs := Classical.choose_spec h
  exact ⟨T.key k, rfl, ContinuationCatalogue.key_identity T k, scalar, hs.1, hs.2⟩

theorem Card.zero_iff {k : RawCardKey m (completeGroup H currentTorsion)}
    (c : Card F H retains oldTorsion currentTorsion sameGroup f k) :
    rawCard H currentTorsion f k = 0 ↔ rawCard F oldTorsion f c.oldKey = 0 := by
  rw [c.equation]
  exact smul_eq_zero_iff_right c.nonzero

/-- Exact nonzero-key transport; no independently chosen new factor tree is
identified with the old once-saved tree at the corresponding ambient key. -/
def fullKey : FullDeckIndex H currentTorsion f → FullDeckIndex F oldTorsion f
  | .inl q => .inl ((change F H retains oldTorsion currentTorsion sameGroup).label q)
  | .inr k =>
      let c := card F H retains oldTorsion currentTorsion sameGroup f k.1
      .inr ⟨c.oldKey, fun hz => k.2 ((c.zero_iff F H retains oldTorsion currentTorsion sameGroup f).mpr hz)⟩

theorem fullKey_ambient (k : FullDeckIndex H currentTorsion f) :
    HistoryCatalogue.embed F oldTorsion f
      (fullKey F H retains oldTorsion currentTorsion sameGroup f k) =
    HistoryCatalogue.embed H currentTorsion f k := by
  cases k with
  | inl q =>
      exact congrArg Sum.inl ((change F H retains oldTorsion currentTorsion sameGroup).label_class q)
  | inr k =>
      change Sum.inr (⟨m,rawKey Subtype.val
        (card F H retains oldTorsion currentTorsion sameGroup f k.1).oldKey⟩ :
        Σ n : ℕ, RawCardKey n (PGL2 L)) = Sum.inr ⟨m,rawKey Subtype.val k.1⟩
      rw [(card F H retains oldTorsion currentTorsion sameGroup f k.1).ambientIdentity]

theorem fullKey_injective : Function.Injective
    (fullKey F H retains oldTorsion currentTorsion sameGroup f) := by
  intro i j he
  apply HistoryCatalogue.embed_injective H currentTorsion f
  rw [← fullKey_ambient F H retains oldTorsion currentTorsion sameGroup f i,
      ← fullKey_ambient F H retains oldTorsion currentTorsion sameGroup f j, he]

include retains sameGroup in
theorem ambientUniverse_unchanged : keyUniverse H currentTorsion f = keyUniverse F oldTorsion f :=
  ContinuationCatalogue.keyUniverse_unchanged retains oldTorsion currentTorsion sameGroup f

/-- The stand-alone zero sentinel is kept separate from nonzero full keys.
Actual zero-valued raw keys are certified by Card.zero_iff. -/
theorem zero_sentinel : (0 : Signature L m) ∈ rawDeck H currentTorsion f := Or.inl rfl

theorem strict_growth_blocks_sameGroup
    (growth : completeGroup F oldTorsion < completeGroup H currentTorsion) :
    ¬ completeGroup H currentTorsion = completeGroup F oldTorsion := by
  intro he
  rw [he] at growth
  exact lt_irrefl _ growth

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
end
