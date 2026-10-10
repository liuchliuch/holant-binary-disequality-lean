import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange
import Holant.Proofs.Closure.ClosureFactorTreeAction

/-! Exact saved-tree embedding followed by an algebraic marked basis.
Prime preservation is the proved factor-descent theorem, not an assumption
that extending the field introduces no new factors. Every old subtree and
address is transported structurally; no replacement tree is selected. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFactorTreeFieldMap
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
variable {L E : Type} [Field L] [Field E]

def tree (phi : L →+* E) {f : AnySignature L} : FactorTree f → FactorTree (mapSignature phi f)
  | .leaf f hf => .leaf _ ((prime_mapSignature_iff phi f).mpr hf)
  | .split s l r => .split (s.map phi) (tree phi l) (tree phi r)

def occurrence (phi : L →+* E) (o : TreeOccurrence L) : TreeOccurrence E :=
  ⟨mapSignature phi o.1,tree phi o.2⟩

@[simp] theorem split_ports (phi : L →+* E) {f a b : AnySignature L} (s : ProperSplit f a b) :
    (s.map phi).ports = s.ports := rfl
@[simp] theorem split_scale (phi : L →+* E) {f a b : AnySignature L} (s : ProperSplit f a b) :
    ((s.map phi).scale : E) = phi (s.scale : L) := rfl

theorem leaves (phi : L →+* E) {f : AnySignature L} (t : FactorTree f) :
    (tree phi t).leaves = t.leaves.map (mapSignature phi) := by
  induction t with
  | leaf => simp [tree,FactorTree.leaves]
  | split s l r ihl ihr => simp [tree,FactorTree.leaves,ihl,ihr]

def slots (phi : L →+* E) {f : AnySignature L} (t : FactorTree f) :
    FactorSaturation.Slots t ≃ FactorSaturation.Slots (tree phi t) := match t with
  | .leaf _ _ => Equiv.refl Unit
  | .split _ l r => Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr (slots phi l) (slots phi r))

theorem slot_exact (phi : L →+* E) {f : AnySignature L}
    (t : FactorTree f) (i : FactorSaturation.Slots t) :
    FactorSaturation.slot (tree phi t) (slots phi t i) = occurrence phi (FactorSaturation.slot t i) := by
  induction t with
  | leaf => rfl
  | split s l r ihl ihr =>
      rcases i with u | (i | i)
      · rfl
      · exact ihl i
      · exact ihr i

theorem path_exact (phi : L →+* E) {f : AnySignature L}
    (t : FactorTree f) (i : FactorSaturation.Slots t) :
    FactorSaturation.path (tree phi t) (slots phi t i) = FactorSaturation.path t i := by
  induction t with
  | leaf => rfl
  | split s l r ihl ihr =>
      rcases i with u | (i | i)
      · rfl
      · exact congrArg (List.cons false) (ihl i)
      · exact congrArg (List.cons true) (ihr i)

def leafSlots (phi : L →+* E) {f : AnySignature L} (t : FactorTree f) :
    FactorSaturation.Leaves t ≃ FactorSaturation.Leaves (tree phi t) := match t with
  | .leaf _ _ => Equiv.refl Unit
  | .split _ l r => Equiv.sumCongr (leafSlots phi l) (leafSlots phi r)

theorem leafSlot_exact (phi : L →+* E) {f : AnySignature L}
    (t : FactorTree f) (i : FactorSaturation.Leaves t) :
    FactorSaturation.leafSlot (tree phi t) (leafSlots phi t i) =
      slots phi t (FactorSaturation.leafSlot t i) := by
  induction t with
  | leaf => rfl
  | split s l r ihl ihr =>
      cases i with
      | inl i => exact congrArg (fun x => Sum.inr (Sum.inl x)) (ihl i)
      | inr i => exact congrArg (fun x => Sum.inr (Sum.inr x)) (ihr i)

theorem leaf_exact (phi : L →+* E) {f : AnySignature L}
    (t : FactorTree f) (i : FactorSaturation.Leaves t) :
    FactorSaturation.leaf (tree phi t) (leafSlots phi t i) = mapSignature phi (FactorSaturation.leaf t i) := by
  unfold FactorSaturation.leaf
  rw [leafSlot_exact,slot_exact]
  rfl

theorem leaf_card (phi : L →+* E) {f : AnySignature L} (t : FactorTree f) :
    Fintype.card (FactorSaturation.Leaves (tree phi t)) = Fintype.card (FactorSaturation.Leaves t) :=
  (Fintype.card_congr (leafSlots phi t)).symm

/-- Original source-field embedding and the SAME marked algebraic basis. -/
def markedTree (phi : L →+* AlgebraicComplex) (B : InvertibleKernel)
    {f : AnySignature L} (t : FactorTree f) :
    FactorTree (ClosureFactorTreeAction.signature B (mapSignature phi f)) :=
  ClosureFactorTreeAction.tree B (tree phi t)

def markedSlots (phi : L →+* AlgebraicComplex) (B : InvertibleKernel)
    {f : AnySignature L} (t : FactorTree f) :
    FactorSaturation.Slots t ≃ FactorSaturation.Slots (markedTree phi B t) :=
  (slots phi t).trans (ClosureFactorTreeAction.slots B (tree phi t))

def markedLeaves (phi : L →+* AlgebraicComplex) (B : InvertibleKernel)
    {f : AnySignature L} (t : FactorTree f) :
    FactorSaturation.Leaves t ≃ FactorSaturation.Leaves (markedTree phi B t) :=
  (leafSlots phi t).trans (ClosureFactorTreeAction.leafSlots B (tree phi t))

theorem marked_slot_exact (phi : L →+* AlgebraicComplex) (B : InvertibleKernel)
    {f : AnySignature L} (t : FactorTree f) (i : FactorSaturation.Slots t) :
    FactorSaturation.slot (markedTree phi B t) (markedSlots phi B t i) =
      ClosureFactorTreeAction.occurrence B (occurrence phi (FactorSaturation.slot t i)) := by
  change FactorSaturation.slot (ClosureFactorTreeAction.tree B (tree phi t))
    (ClosureFactorTreeAction.slots B (tree phi t) (slots phi t i)) = _
  rw [ClosureFactorTreeAction.slot_exact,slot_exact]

theorem marked_path_exact (phi : L →+* AlgebraicComplex) (B : InvertibleKernel)
    {f : AnySignature L} (t : FactorTree f) (i : FactorSaturation.Slots t) :
    FactorSaturation.path (markedTree phi B t) (markedSlots phi B t i) = FactorSaturation.path t i :=
  (ClosureFactorTreeAction.path_exact B (tree phi t) (slots phi t i)).trans (path_exact phi t i)

theorem marked_leaf_exact (phi : L →+* AlgebraicComplex) (B : InvertibleKernel)
    {f : AnySignature L} (t : FactorTree f) (i : FactorSaturation.Leaves t) :
    FactorSaturation.leaf (markedTree phi B t) (markedLeaves phi B t i) =
      ClosureFactorTreeAction.signature B (mapSignature phi (FactorSaturation.leaf t i)) := by
  change FactorSaturation.leaf (ClosureFactorTreeAction.tree B (tree phi t))
    (ClosureFactorTreeAction.leafSlots B (tree phi t) (leafSlots phi t i)) = _
  rw [ClosureFactorTreeAction.leaf_exact,leaf_exact]

theorem marked_leaf_card (phi : L →+* AlgebraicComplex) (B : InvertibleKernel)
    {f : AnySignature L} (t : FactorTree f) :
    Fintype.card (FactorSaturation.Leaves (markedTree phi B t)) = Fintype.card (FactorSaturation.Leaves t) :=
  (Fintype.card_congr (markedLeaves phi B t)).symm

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFactorTreeFieldMap
end
