import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticParityFourierAssignments

/-! The literal Fourier rows are an ordinary finite signature table. Its
conditional partition over the actual54 addresses is the cubic phase times
the exact fixed nonzero characteristic-zero scale2^25. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourierTyped
open Holant Holant.Tractable
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativeOcticParityFourier OrdinaryNegativeOcticParityFourierSemantics
open OrdinaryNegativeOcticParityFourierAssignments
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace S
export StableHigherCurrentOrdinarySquare (rowValue weight extend)
end S
variable {K : Type*} [CommRing K]

def first (i : Fin 3) : Fin (arity i.val) := ⟨0,by unfold arity; split_ifs <;> omega⟩
def second (i : Fin 3) (hi : i.val=0) : Fin (arity i.val) := ⟨1,by simp [arity,hi]⟩

def table (z : K) (i : Fin 3) : Signature K (arity i.val) := fun x=>
  if h : i.val=0 then character (x (first i)) (x (second i h))
  else if i.val=1 then z^(x (first i)).toNat
  else if x (first i) then 0 else 1

theorem typed_row (z : K) (w : ℕ → Bool) (r : Factor) (hr : r.1<3) :
    S.rowValue (table z) r w=OrdinaryNegativeOcticParityFourierSemantics.rowValue z w r := by
  unfold StableHigherCurrentOrdinarySquare.rowValue
  rw [dif_pos hr]
  unfold table OrdinaryNegativeOcticParityFourierSemantics.rowValue
  simp only [first,second,Fin.val_mk]
  split_ifs <;> rfl

private theorem read_bound (r : Factor) (hr : r∈factors) (j : ℕ) : r.2.getD j 0<54 := by
  have h := (all_addresses_valid r hr).2.2
  by_cases hj : j<r.2.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    decide

theorem row_extended (z : K) (x : Fin 3 → Bool) (y : Free)
    (r : Factor) (hr : r∈factors) :
    S.rowValue (table z) r (S.extend (word x y).val)=
      OrdinaryNegativeOcticParityFourierSemantics.rowValue z (assignment x y.1 y.2) r := by
  rw [typed_row z _ r (all_addresses_valid r hr).1]
  have h (j : ℕ) : S.extend (word x y).val (r.2.getD j 0)=
      assignment x y.1 y.2 (r.2.getD j 0) := by
    simp only [StableHigherCurrentOrdinarySquare.extend,dif_pos (read_bound r hr j),word]
  unfold OrdinaryNegativeOcticParityFourierSemantics.rowValue
  rw [h 0,h 1]

theorem weight_extended (z : K) (x : Fin 3 → Bool) (y : Free) :
    S.weight (table z) factors (S.extend (word x y).val)=
      OrdinaryNegativeOcticParityFourierSemantics.weight z (assignment x y.1 y.2) factors := by
  unfold StableHigherCurrentOrdinarySquare.weight OrdinaryNegativeOcticParityFourierSemantics.weight
  apply congrArg List.prod
  apply List.map_congr_left
  intro r hr
  exact row_extended z x y r hr

/-- The summation domain is all actual54-bit words with the three logical
ports fixed. Every private assignment is counted exactly once. -/
def conditionalValue (z : K) (x : Fin 3 → Bool) : K :=
  ∑w : Words x,S.weight (table z) factors (S.extend w.val)

theorem conditional_cubic (z : K) (hfour : z^4= -1) (x : Fin 3 → Bool) :
    conditionalValue z x=2^25*OrdinaryNegativeCubicCore.cubic x := by
  unfold conditionalValue
  rw [sum_words]
  simp_rw [weight_extended]
  rw [Fintype.sum_prod_type]
  exact rows_cubic z hfour x
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourierTyped
end
