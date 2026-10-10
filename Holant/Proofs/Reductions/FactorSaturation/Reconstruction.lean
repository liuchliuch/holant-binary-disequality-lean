import Holant.Proofs.Reductions.FactorSaturation.StoredForest


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation
open scoped BigOperators
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {K : Type} [Field K]

def Leaves {f : AnySignature K} : FactorTree f → Type
  | .leaf _ _ => Unit
  | .split _ l r => Leaves l ⊕ Leaves r
instance leavesFintype {f : AnySignature K} (t : FactorTree f) : Fintype (Leaves t) := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | split s l r il ir =>
      letI := il
      letI := ir
      exact inferInstanceAs (Fintype (Leaves l ⊕ Leaves r))

def leafSlot {f : AnySignature K} (t : FactorTree f) : Leaves t → Slots t :=
  match t with
  | .leaf _ _ => id
  | .split _ l r => Sum.elim (fun i => .inr (.inl (leafSlot l i)))
      (fun i => .inr (.inr (leafSlot r i)))
def leaf {f : AnySignature K} (t : FactorTree f) (i : Leaves t) : AnySignature K :=
  (slot t (leafSlot t i)).1

theorem leaf_mem {f : AnySignature K} (t : FactorTree f) (i : Leaves t) : leaf t i ∈ t.leaves := by
  induction t with
  | leaf => exact Multiset.mem_singleton_self _
  | split s l r il ir =>
      cases i with
      | inl i => exact Multiset.mem_add.mpr (Or.inl (il i))
      | inr i => exact Multiset.mem_add.mpr (Or.inr (ir i))

theorem leaf_prime {f : AnySignature K} (t : FactorTree f) (i : Leaves t) : Prime (leaf t i) :=
  t.leaves_prime _ (leaf_mem t i)

abbrev LeafPorts {f : AnySignature K} (t : FactorTree f) := Σ i : Leaves t, Fin (leaf t i).1

def leafPorts {f : AnySignature K} (t : FactorTree f) : LeafPorts t ≃ Fin f.1 :=
  match t with
  | .leaf _ _ => {
      toFun := fun p => p.2
      invFun := fun i => ⟨(),i⟩
      left_inv := by rintro ⟨u,i⟩; cases u; rfl
      right_inv := fun _ => rfl }
  | .split s l r =>
      (Equiv.sumSigmaDistrib (fun i => Fin (leaf (.split s l r) i).1)).trans
        ((Equiv.sumCongr (leafPorts l) (leafPorts r)).trans s.ports)

def treeScale {f : AnySignature K} : FactorTree f → Kˣ
  | .leaf _ _ => 1
  | .split s l r => s.scale * treeScale l * treeScale r

theorem reconstruct {f : AnySignature K} (t : FactorTree f) (x : Fin f.1 → Bool) :
    f.2 x = (treeScale t : K) * ∏ i : Leaves t,
      (leaf t i).2 (fun p => x (leafPorts t ⟨i,p⟩)) := by
  induction t with
  | leaf f hp =>
      change f.2 x = 1 * ∏ _i : Unit, f.2 x
      simp
  | split s l r il ir =>
      rw [s.equation]
      dsimp only
      rw [il (fun i => x (s.ports (.inl i))), ir (fun i => x (s.ports (.inr i)))]
      simp only [treeScale, Units.val_mul, Leaves, leavesFintype, Fintype.prod_sum_type]
      change _ = ((s.scale : K) * (treeScale l : K) * (treeScale r : K)) *
        ((∏ i : Leaves l, (leaf l i).2 (fun p => x (s.ports (.inl (leafPorts l ⟨i,p⟩))))) *
         (∏ i : Leaves r, (leaf r i).2 (fun p => x (s.ports (.inr (leafPorts r ⟨i,p⟩))))))
      ring

theorem total_leaf_arity {f : AnySignature K} (t : FactorTree f) :
    (∑ i : Leaves t, (leaf t i).1) = f.1 := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr (leafPorts t)

theorem leaf_count_le_arity {f : AnySignature K} (t : FactorTree f) (hp : 0 < f.1) :
    Fintype.card (Leaves t) ≤ f.1 := by
  calc
    Fintype.card (Leaves t) = ∑ _i : Leaves t, (1 : ℕ) := by simp
    _ ≤ ∑ i : Leaves t, (leaf t i).1 := by
      apply Finset.sum_le_sum
      intro i _
      exact stored_positive (slot_stored t (leafSlot t i)) hp
    _ = f.1 := total_leaf_arity t

theorem slots_card {f : AnySignature K} (t : FactorTree f) :
    Fintype.card (Slots t) + 1 = 2 * Fintype.card (Leaves t) := by
  induction t with
  | leaf => simp [Slots, Leaves, slotsFintype, leavesFintype]
  | split s l r il ir =>
      simp only [Slots, Leaves, slotsFintype, leavesFintype, Fintype.card_sum, Fintype.card_unit]
      omega

theorem slots_bound {f : AnySignature K} (t : FactorTree f) (hp : 0 < f.1) :
    Fintype.card (Slots t) + 1 ≤ 2 * f.1 := by
  rw [slots_card]
  exact Nat.mul_le_mul_left 2 (leaf_count_le_arity t hp)

end Holant.LocalDrafts.Hardness.FactorSaturation
