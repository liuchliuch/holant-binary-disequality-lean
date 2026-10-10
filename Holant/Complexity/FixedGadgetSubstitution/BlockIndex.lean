import Holant.Complexity.FixedGadgetSubstitution.Raw
import Mathlib.Logic.Equiv.Fin.Basic

/-! The arithmetic block indices used by the raw replacement compiler are an
explicit bijection with original-copy/local-occurrence coordinates. -/
namespace Holant.Complexity.FixedGadgetSubstitution
set_option backward.isDefEq.respectTransparency false

/-- Split a dependent finite tuple at its first occurrence. -/
def sigmaFinCons {n : ℕ} (f : Fin (n+1) → Type*) :
    (Σ i, f i) ≃ (f 0 ⊕ (Σ i : Fin n, f i.succ)) where
  toFun p := Fin.cases (fun x => Sum.inl x) (fun i x => Sum.inr ⟨i,x⟩) p.1 p.2
  invFun := Sum.elim (fun x => ⟨0,x⟩) (fun p => ⟨p.1.succ,p.2⟩)
  left_inv p := by rcases p with ⟨i,x⟩; induction i using Fin.cases <;> rfl
  right_inv p := by cases p <;> rfl

abbrev Blocks {α : Type} (size : α → ℕ) (rows : List α) :=
  Σ i : Fin rows.length, Fin (size (rows.get i))

/-- Every local occurrence receives the cumulative preceding block length plus
its local index. The inverse also exists when some or all blocks are empty. -/
def blockEquiv {α : Type} (size : α → ℕ) :
    (rows : List α) → Blocks size rows ≃ Fin (rows.map size).sum
  | [] => {
      toFun p := Fin.elim0 p.1
      invFun p := Fin.elim0 p
      left_inv p := Fin.elim0 p.1
      right_inv p := Fin.elim0 p }
  | row :: rows => (sigmaFinCons (fun i => Fin (size ((row::rows).get i)))).trans
      ((Equiv.sumCongr (Equiv.refl _) (blockEquiv size rows)).trans finSumFinEquiv)

 theorem blockEquiv_val {α : Type} (size : α → ℕ) (rows : List α)
    (p : Blocks size rows) :
    (blockEquiv size rows p).val = ((rows.take p.1.val).map size).sum+p.2.val := by
  induction rows with
  | nil => exact Fin.elim0 p.1
  | cons row rows ih =>
    rcases p with ⟨i,j⟩
    induction i using Fin.cases with
    | zero =>
      change j.val = 0+j.val
      omega
    | succ i =>
      change size row + (blockEquiv size rows ⟨i,j⟩).val =
        size row + ((rows.take i.val).map size).sum+j.val
      rw [ih]
      exact (Nat.add_assoc _ _ _).symm

/-- Exact target-record position for the block concatenation, not just a bound. -/
 theorem get_flatten_blocks {α β : Type} (rows : List α) (f : α → List β)
    (p : Blocks (fun a => (f a).length) rows) :
    ((rows.map f).flatten)[(blockEquiv (fun a => (f a).length) rows p).val]'(by
      simpa [List.length_flatten,List.map_map,Function.comp_def] using
        (blockEquiv (fun a => (f a).length) rows p).isLt) = (f (rows.get p.1)).get p.2 := by
  induction rows with
  | nil => exact Fin.elim0 p.1
  | cons row rows ih =>
    rcases p with ⟨i,j⟩
    induction i using Fin.cases with
    | zero =>
      change Fin (f row).length at j
      change (f row ++ (rows.map f).flatten)[j.val] = (f row).get j
      rw [List.getElem_append_left j.isLt]
      rfl
    | succ i =>
      change Fin (f (rows.get i)).length at j
      have hb : (blockEquiv (fun a => (f a).length) rows ⟨i,j⟩).val <
          (rows.map f).flatten.length := by
        simpa [List.length_flatten,List.map_map,Function.comp_def] using
          (blockEquiv (fun a => (f a).length) rows ⟨i,j⟩).isLt
      change (f row ++ (rows.map f).flatten)[(f row).length+
        (blockEquiv (fun a => (f a).length) rows ⟨i,j⟩).val]'(by simpa only [List.length_append] using Nat.add_lt_add_left hb (f row).length) = (f (rows.get i)).get j
      rw [List.getElem_append_right (by omega)]
      simpa using ih ⟨i,j⟩

end Holant.Complexity.FixedGadgetSubstitution
