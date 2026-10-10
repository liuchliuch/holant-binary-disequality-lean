import Holant.Proofs.Closure.ContinuationTransport
import Holant.Proofs.Closure.HistoryCatalogue

/-! At an unchanged actual group and the SAME literal core, regenerated
representative choices do not create new literal ambient key names. The
nonzero raw-key filter is transported by the explicit nonzero card scalar.
No newly chosen factor tree is substituted for the frozen tree at that key. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ContinuationCatalogue
open Holant Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ContinuationTransport HistoryCatalogue
variable {L : Type*} [Field L] [NumberField L]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq (Key L) := Classical.decEq _

theorem key_identity {F G : SignatureFamily L} {hF : ResidualTorsion F}
    {hG : ResidualTorsion G} (T : RepresentativeChange F hF G hG) {m : ℕ}
    (k : RawCardKey m (completeGroup G hG)) :
    rawKey Subtype.val (T.key k) = rawKey Subtype.val k := by
  apply Prod.ext
  · funext i
    cases hδ : k.1 i with
    | none => simp only [rawKey, RepresentativeChange.key, RepresentativeChange.dressing,
        hδ, Option.map_none]
    | some p => simp only [rawKey, RepresentativeChange.key, RepresentativeChange.dressing,
        hδ, Option.map_some, T.label_class]
  · exact Prod.ext rfl (Prod.ext (T.label_class k.2.2.1) rfl)

theorem keyUniverse_subset {F G : SignatureFamily L} {hF : ResidualTorsion F}
    {hG : ResidualTorsion G} (T : RepresentativeChange F hF G hG) {m : ℕ}
    (f : Signature L (m+2)) : keyUniverse G hG f ⊆ keyUniverse F hF f := by
  intro j hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  cases k with
  | inl q =>
      refine Finset.mem_image.mpr ⟨.inl (T.label q), mem_fullDeckUniverse F hF f _, ?_⟩
      exact congrArg Sum.inl (T.label_class q)
  | inr k =>
      obtain ⟨c, hc, hcard⟩ := rawCard_transport T f k.1
      have hnonzero : rawCard F hF f (T.key k.1) ≠ 0 := by
        intro hz
        apply k.2
        rw [hcard, hz, smul_zero]
      refine Finset.mem_image.mpr ⟨.inr ⟨T.key k.1, hnonzero⟩, mem_fullDeckUniverse F hF f _, ?_⟩
      change Sum.inr (⟨m, rawKey Subtype.val (T.key k.1)⟩ : Σ n : ℕ, RawCardKey n (PGL2 L)) =
        Sum.inr ⟨m, rawKey Subtype.val k.1⟩
      rw [key_identity T k.1]

/-- Same group/core stratum has exactly the same FULL literal key set,
including the nonzero filter, every orientation and residual port order. -/
theorem keyUniverse_unchanged {F G : SignatureFamily L} (hFG : F ⊆ G)
    (hF : ResidualTorsion F) (hG : ResidualTorsion G)
    (he : completeGroup G hG = completeGroup F hF) {m : ℕ}
    (f : Signature L (m+2)) : keyUniverse G hG f = keyUniverse F hF f := by
  let T := representativeChange hFG hF hG he
  exact Finset.Subset.antisymm (keyUniverse_subset T f) (keyUniverse_subset (T.reverse he) f)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ContinuationCatalogue
end
