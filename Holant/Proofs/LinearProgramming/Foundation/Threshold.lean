import Holant.Proofs.LinearProgramming.Foundation.Parsing
import Mathlib.Algebra.BigOperators.Fin

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Exact non-strict threshold reduction. For D>=1, adjoining one bounded slack
and D*x_j-(D-1)*t=1 is equivalent to x_j>=1/D. PositiveThreshold combines this reduction with the proved uniform gap, and
the complete backend supplies the bounded-feasibility machine. The value D
is never an assumed positive-coordinate witness.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Threshold
open Holant.Complexity Codec
open scoped BigOperators
noncomputable section

def coefficients (d : Raw) (j : Fin d.dimension) (D : ℕ) :
    Fin (d.rowCount+1) → Fin (d.dimension+1) → ℤ :=
  Fin.lastCases
    (Fin.lastCases (1-(D:ℤ)) (fun k => if k=j then (D:ℤ) else 0))
    (fun i => Fin.lastCases 0 (d.coefficient i))
def constants (d : Raw) : Fin (d.rowCount+1) → ℤ := Fin.lastCases 1 d.constant
def value (d : Raw) (j : Fin d.dimension) (D : ℕ) : Input :=
  pack (d.rowCount+1) (d.dimension+1) (coefficients d j D) (constants d)
def project (d : Raw) (y : Fin (d.dimension+1) → ℚ) : Fin d.dimension → ℚ :=
  fun k => y k.castSucc

theorem equations (d : Raw) (j : Fin d.dimension) (D : ℕ) (y : Fin (d.dimension+1) → ℚ) :
    (∀ i, ∑ k, (coefficients d j D i k : ℚ)*y k = constants d i) ↔
      (∀ i, ∑ k, (d.coefficient i k : ℚ)*project d y k = d.constant i) ∧
        (D:ℚ)*project d y j+(1-(D:ℚ))*y (Fin.last d.dimension)=1 := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [coefficients,constants,Fin.sum_univ_castSucc,project] using h i.castSucc
    · simpa [coefficients,constants,Fin.sum_univ_castSucc,project] using h (Fin.last d.rowCount)
  · rintro ⟨ho,hn⟩ i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [coefficients,constants,Fin.sum_univ_castSucc,project] using hn
    · simpa [coefficients,constants,Fin.sum_univ_castSucc,project] using ho i

theorem feasible (d : Raw) (j : Fin d.dimension) (D : ℕ) (y : Fin (d.dimension+1) → ℚ) :
    Feasible (value d j D).val y ↔ Feasible d (project d y) ∧
      0 ≤ y (Fin.last d.dimension) ∧ y (Fin.last d.dimension) ≤ 1 ∧
      (D:ℚ)*project d y j+(1-(D:ℚ))*y (Fin.last d.dimension)=1 := by
  unfold value
  rw [pack_feasible,equations]
  constructor
  · rintro ⟨⟨ho,he⟩,hb⟩
    exact ⟨⟨ho,fun k => hb k.castSucc⟩,(hb _).1,(hb _).2,he⟩
  · rintro ⟨⟨ho,hb⟩,ht0,ht1,he⟩
    refine ⟨⟨ho,he⟩,?_⟩
    intro k
    exact Fin.lastCases ⟨ht0,ht1⟩ (fun k => hb k) k

/-- The witness slack is derived algebraically; degeneracy D=1 is separate. -/
theorem slack_exists (D : ℕ) (hD : 1≤D) (q : ℚ) (hq : q≤1) (hl : 1/(D:ℚ)≤q) :
    ∃ t : ℚ, 0≤t ∧ t≤1 ∧ (D:ℚ)*q+(1-(D:ℚ))*t=1 := by
  have hd : (0:ℚ)<D := by exact_mod_cast (show 0<D by omega)
  have hlow : 1≤(D:ℚ)*q := by
    have h := (div_le_iff₀ hd).mp hl
    nlinarith
  by_cases he : D=1
  · subst D
    refine ⟨0,le_rfl,by norm_num,?_⟩
    norm_num at hlow ⊢
    exact le_antisymm hq hlow
  · have hd1 : (1:ℚ)<D := by exact_mod_cast (show 1<D by omega)
    have hp : (0:ℚ)<(D:ℚ)-1 := sub_pos.mpr hd1
    refine ⟨((D:ℚ)*q-1)/((D:ℚ)-1),div_nonneg (by linarith) hp.le,?_,?_⟩
    · apply (div_le_iff₀ hp).mpr
      nlinarith
    · have heq := div_mul_cancel₀ ((D:ℚ)*q-1) (ne_of_gt hp)
      nlinarith

theorem exists_iff (d : Raw) (j : Fin d.dimension) (D : ℕ) (hD : 1≤D) :
    (∃ y, Feasible (value d j D).val y) ↔
      ∃ x, Feasible d x ∧ 1/(D:ℚ)≤x j := by
  have hd : (0:ℚ)<D := by exact_mod_cast (show 0<D by omega)
  have hd1 : (1:ℚ)≤D := by exact_mod_cast hD
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hx,ht0,ht1,he⟩ := (feasible d j D y).mp hy
    refine ⟨project d y,hx,(div_le_iff₀ hd).mpr ?_⟩
    nlinarith
  · rintro ⟨x,hx,hj⟩
    obtain ⟨t,ht0,ht1,ht⟩ := slack_exists D hD (x j) (hx.2 j).2 hj
    refine ⟨Fin.snoc x t,(feasible d j D _).mpr ?_⟩
    have hproject : project d (Fin.snoc x t) = x := by
      funext k
      exact Fin.snoc_castSucc (α := fun _ => ℚ) t x k
    change Feasible d (project d (Fin.snoc x t)) ∧
      0 ≤ Fin.snoc (α := fun _ => ℚ) x t (Fin.last d.dimension) ∧
      Fin.snoc (α := fun _ => ℚ) x t (Fin.last d.dimension) ≤ 1 ∧
      (D:ℚ) * project d (Fin.snoc x t) j +
        (1-(D:ℚ)) * Fin.snoc (α := fun _ => ℚ) x t (Fin.last d.dimension) = 1
    rw [hproject]
    simpa only [Fin.snoc_last] using
      And.intro hx (And.intro ht0 (And.intro ht1 ht))

theorem implies_positive (d : Raw) (j : Fin d.dimension) (D : ℕ) (hD : 1≤D)
    (h : ∃ y, Feasible (value d j D).val y) : Positive d j := by
  obtain ⟨x,hx,hj⟩ := (exists_iff d j D hD).mp h
  refine ⟨x,hx,lt_of_lt_of_le ?_ hj⟩
  positivity

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Threshold
