import Holant.Proofs.FiniteGroups.Stabilization.FullRetainedDeck
import Holant.Proofs.Closure.QueueTagged

/-! A common ambient key type for saved all-arity histories.  The embedding
retains the literal raw key, including every orientation and port permutation.
Equal card tables do not identify keys.  The field is a parameter throughout.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistoryCatalogue
open Holant Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L : Type*} [Field L] [NumberField L]
attribute [local instance] Classical.propDecidable

abbrev Key (L : Type*) [Field L] := PGL2 L ⊕ (Σ m : ℕ, RawCardKey m (PGL2 L))
local instance : DecidableEq (Key L) := Classical.decEq _

def rawKey {H I : Type*} {m : ℕ} (e : H → I) (k : RawCardKey m H) : RawCardKey m I :=
  (fun i => (k.1 i).map (fun p => (e p.1, p.2)), k.2.1, e k.2.2.1, k.2.2.2)

theorem pairOption_injective {H I : Type*} (e : H → I) (he : Function.Injective e) :
    Function.Injective (fun o : Option (H × Bool) => o.map (fun p => (e p.1, p.2))) := by
  intro x y h
  cases x with
  | none => cases y <;> simpa using h
  | some x =>
      cases y with
      | none => simp at h
      | some y =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          exact congrArg some (Prod.ext (he h.1) h.2)

theorem rawKey_injective {H I : Type*} {m : ℕ} (e : H → I) (he : Function.Injective e) :
    Function.Injective (rawKey (m:=m) e) := by
  intro x y h
  rcases x with ⟨δx, px, qx, bx⟩
  rcases y with ⟨δy, py, qy, by'⟩
  have hδ := congrArg Prod.fst h
  have hp := congrArg (fun k => k.2.1) h
  have hq := congrArg (fun k => k.2.2.1) h
  have hb := congrArg (fun k => k.2.2.2) h
  have hδ' : δx = δy := by
    funext i
    exact pairOption_injective e he (congrFun hδ i)
  have hq' : qx = qy := he hq
  cases hδ'
  cases hp
  cases hq'
  cases hb
  rfl

def embed {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) : FullDeckIndex F hF f → Key L
  | .inl q => .inl q.1
  | .inr k => .inr ⟨m, rawKey Subtype.val k.1⟩

theorem embed_injective {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) : Function.Injective (embed F hF f) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
      | inr y => cases h
  | inr x =>
      cases y with
      | inl y => cases h
      | inr y =>
          have hk : rawKey Subtype.val x.1 = rawKey Subtype.val y.1 := by
            simpa only [embed, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
          exact congrArg Sum.inr (Subtype.ext (rawKey_injective Subtype.val Subtype.val_injective hk))

def keyUniverse {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) : Finset (Key L) :=
  (fullDeckUniverse F hF f).image (embed F hF f)

def root {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) : Key L → TreeOccurrence L := by
  letI : Nonempty (FullDeckIndex F hF f) := ⟨.inl 1⟩
  exact fun k => fullDeckRoot F hF f (Function.invFun (embed F hF f) k)

theorem root_binding {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : FullDeckIndex F hF f) :
    root F hF f (embed F hF f k) = fullDeckRoot F hF f k := by
  unfold root
  rw [Function.leftInverse_invFun (embed_injective F hF f)]

theorem key_covered {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : FullDeckIndex F hF f) :
    embed F hF f k ∈ keyUniverse F hF f := by
  exact Finset.mem_image.mpr ⟨k, mem_fullDeckUniverse F hF f k, rfl⟩

structure Exhausted {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) where
  tagged : QueueTagged.Exhaustion (QueueTagged.State.initial (U:=keyUniverse F hF f) (root F hF f))

def Exhausted.final {m : ℕ} {F : SignatureFamily L} {hF : ResidualTorsion F}
    {f : Signature L (m+2)} (E : Exhausted F hF f) : FrozenQueue L (keyUniverse F hF f) :=
  E.tagged.finalState.queue

def Exhausted.trace {m : ℕ} {F : SignatureFamily L} {hF : ResidualTorsion F}
    {f : Signature L (m+2)} (E : Exhausted F hF f) :
    TokenExecution.Trace (FrozenQueue.initial (keyUniverse F hF f) (root F hF f)) E.final :=
  E.tagged.trace.projected

theorem Exhausted.run {m : ℕ} {F : SignatureFamily L} {hF : ResidualTorsion F}
    {f : Signature L (m+2)} (E : Exhausted F hF f) :
    FrozenQueue.Runs (FrozenQueue.initial (keyUniverse F hF f) (root F hF f)) E.final :=
  E.trace.runs

theorem Exhausted.empty {m : ℕ} {F : SignatureFamily L} {hF : ResidualTorsion F}
    {f : Signature L (m+2)} (E : Exhausted F hF f) : E.final.todo = ∅ := E.tagged.exhausted

theorem Exhausted.allDone {m : ℕ} {F : SignatureFamily L} {hF : ResidualTorsion F}
    {f : Signature L (m+2)} (E : Exhausted F hF f) : E.final.done = keyUniverse F hF f :=
  FrozenQueue.done_eq_universe_of_exhausted E.final E.empty

def taggedExecution {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) :=
  QueueTagged.initialExhaustion (U := keyUniverse F hF f) (root F hF f)

def exhaust {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) : Exhausted F hF f := ⟨taggedExecution F hF f⟩

theorem exhausted_coverage {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : FullDeckIndex F hF f) :
    embed F hF f k ∈ (exhaust F hF f).final.done := by
  rw [(exhaust F hF f).allDone]
  exact key_covered F hF f k

theorem occurrence_coverage {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : FullDeckIndex F hF f) :
    (QueueTagged.initialExposed (U := keyUniverse F hF f) (root F hF f) (embed F hF f k)).map Prod.snd =
      OccurrenceSchedule.leafOccurrences (fullDeckRoot F hF f k).2 := by
  rw [QueueTagged.initial_leaf_addresses _ _ (key_covered F hF f k),
    QueueTagged.treeLeaves_project, root_binding]

theorem stored_node_coverage {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : FullDeckIndex F hF f) :
    (QueueTagged.initialVisited (U := keyUniverse F hF f) (root F hF f) (embed F hF f k)).map Prod.snd =
      TokenExecution.nodeOccurrences (fullDeckRoot F hF f k).2 := by
  rw [QueueTagged.initial_node_addresses _ _ (key_covered F hF f k),
    QueueTagged.treeNodes_project, root_binding]

theorem same_trace_leaf_projection {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : Key L) :
    (QueueTagged.initialExposed (U:=keyUniverse F hF f) (root F hF f) k).map Prod.snd =
      TokenExecution.closedLeaves (root F hF f k) + (exhaust F hF f).trace.exposed k :=
  QueueTagged.initialExposed_project _ _

theorem same_trace_node_projection {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : Key L) :
    (QueueTagged.initialVisited (U:=keyUniverse F hF f) (root F hF f) k).map Prod.snd =
      TokenExecution.closedNodes (root F hF f k) + (exhaust F hF f).trace.visited k :=
  QueueTagged.initialVisited_project _ _

theorem leaf_address_coverage {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : FullDeckIndex F hF f) :
    QueueTagged.initialExposed (U:=keyUniverse F hF f) (root F hF f) (embed F hF f k) =
      QueueTagged.treeLeaves (fullDeckRoot F hF f k).2 [] := by
  rw [QueueTagged.initial_leaf_addresses _ _ (key_covered F hF f k), root_binding]

theorem node_address_coverage {m : ℕ} (F : SignatureFamily L) (hF : ResidualTorsion F)
    (f : Signature L (m+2)) (k : FullDeckIndex F hF f) :
    QueueTagged.initialVisited (U:=keyUniverse F hF f) (root F hF f) (embed F hF f k) =
      QueueTagged.treeNodes (fullDeckRoot F hF f k).2 [] := by
  rw [QueueTagged.initial_node_addresses _ _ (key_covered F hF f k), root_binding]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistoryCatalogue
end
