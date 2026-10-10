import Holant.Proofs.LinearProgramming.Interface
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
General rational upper thresholds, with one actual bounded slack variable.
For 0<=p<=q and q>0, q*x_j+p*s=p represents x_j<=p/q exactly.
The p=0 degeneracy is proved separately. These are reductions, not an
optimization oracle and not a reinterpretation of a thickened center.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Codec
open scoped BigOperators
namespace Threshold

def coefficients (d : Raw) (j : Fin d.dimension) (p q : ℕ) :
    Fin (d.rowCount+1) → Fin (d.dimension+1) → ℤ :=
  Fin.lastCases (Fin.lastCases (p:ℤ) (fun k => if k=j then (q:ℤ) else 0))
    (fun i => Fin.lastCases 0 (d.coefficient i))
def constants (d : Raw) (p : ℕ) : Fin (d.rowCount+1) → ℤ := Fin.lastCases (p:ℤ) d.constant
def value (d : Raw) (j : Fin d.dimension) (p q : ℕ) : Input :=
  pack (d.rowCount+1) (d.dimension+1) (coefficients d j p q) (constants d p)
def project (d : Raw) (y : Fin (d.dimension+1) → ℚ) : Fin d.dimension → ℚ :=
  fun k => y k.castSucc

theorem equations (d : Raw) (j : Fin d.dimension) (p q : ℕ) (y : Fin (d.dimension+1) → ℚ) :
    (∀ i, ∑ k, (coefficients d j p q i k : ℚ)*y k = constants d p i) ↔
      (∀ i, ∑ k, (d.coefficient i k : ℚ)*project d y k = d.constant i) ∧
        (q:ℚ)*project d y j+(p:ℚ)*y (Fin.last d.dimension)=p := by
  constructor
  · intro h
    exact ⟨fun i => by simpa [coefficients,constants,project,Fin.sum_univ_castSucc] using h i.castSucc,
      by simpa [coefficients,constants,project,Fin.sum_univ_castSucc] using h (Fin.last d.rowCount)⟩
  · rintro ⟨ho,hn⟩ i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [coefficients,constants,project,Fin.sum_univ_castSucc] using hn
    · simpa [coefficients,constants,project,Fin.sum_univ_castSucc] using ho i

theorem feasible (d : Raw) (j : Fin d.dimension) (p q : ℕ) (y : Fin (d.dimension+1) → ℚ) :
    Feasible (value d j p q).val y ↔ Feasible d (project d y) ∧
      0≤y (Fin.last d.dimension) ∧ y (Fin.last d.dimension)≤1 ∧
      (q:ℚ)*project d y j+(p:ℚ)*y (Fin.last d.dimension)=p := by
  change Feasible (pack (d.rowCount+1) (d.dimension+1)
    (coefficients d j p q) (constants d p)).val y ↔ _
  rw [pack_feasible,equations]
  constructor
  · rintro ⟨⟨ho,he⟩,hb⟩
    exact ⟨⟨ho,fun k => hb k.castSucc⟩,(hb _).1,(hb _).2,he⟩
  · rintro ⟨⟨ho,hb⟩,ht0,ht1,he⟩
    exact ⟨⟨ho,he⟩,fun k => Fin.lastCases ⟨ht0,ht1⟩ (fun k => hb k) k⟩

theorem slack_exists (p q : ℕ) (hq : 0<q) (a : ℚ) (ha : 0≤a) (hu : a≤(p:ℚ)/q) :
    ∃ t : ℚ, 0≤t ∧ t≤1 ∧ (q:ℚ)*a+(p:ℚ)*t=p := by
  have hq' : (0:ℚ)<q := by exact_mod_cast hq
  have hqa : (q:ℚ)*a≤p := by
    have h := (le_div_iff₀ hq').mp hu
    simpa [mul_comm] using h
  by_cases hp : p=0
  · subst p
    have hz : a=0 := by simpa using le_antisymm (by simpa using hu) ha
    exact ⟨0,le_rfl,by norm_num,by simp [hz]⟩
  · have hp' : (0:ℚ)<p := by exact_mod_cast (Nat.pos_of_ne_zero hp)
    refine ⟨((p:ℚ)-(q:ℚ)*a)/p,div_nonneg (by linarith) hp'.le,?_,?_⟩
    · apply (div_le_iff₀ hp').mpr
      nlinarith
    · have he := div_mul_cancel₀ ((p:ℚ)-(q:ℚ)*a) (ne_of_gt hp')
      nlinarith

theorem exists_iff (d : Raw) (j : Fin d.dimension) (p q : ℕ) (hq : 0<q) :
    (∃ y, Feasible (value d j p q).val y) ↔ ∃ x, Feasible d x ∧ x j≤(p:ℚ)/q := by
  have hq' : (0:ℚ)<q := by exact_mod_cast hq
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hx,ht0,ht1,he⟩ := (feasible d j p q y).mp hy
    refine ⟨project d y,hx,(le_div_iff₀ hq').mpr ?_⟩
    have hp : (0:ℚ)≤p := Nat.cast_nonneg p
    nlinarith
  · rintro ⟨x,hx,hj⟩
    obtain ⟨t,ht0,ht1,ht⟩ := slack_exists p q hq (x j) (hx.2 j).1 hj
    refine ⟨Fin.snoc x t,(feasible d j p q _).mpr ?_⟩
    have hproject : project d (Fin.snoc x t) = x := by
      funext k
      exact Fin.snoc_castSucc (α := fun _ => ℚ) t x k
    change Feasible d (project d (Fin.snoc x t)) ∧
      0 ≤ Fin.snoc (α := fun _ => ℚ) x t (Fin.last d.dimension) ∧
      Fin.snoc (α := fun _ => ℚ) x t (Fin.last d.dimension) ≤ 1 ∧
      (q:ℚ) * project d (Fin.snoc x t) j +
        (p:ℚ) * Fin.snoc (α := fun _ => ℚ) x t (Fin.last d.dimension) = p
    rw [hproject]
    simpa only [Fin.snoc_last] using
      And.intro hx (And.intro ht0 (And.intro ht1 ht))

/-- Exact coordinate fixation keeps the original variable set. This will be
used by the scalar extractor and successive-face point machine. -/
def fixedCoefficients (d : Raw) (j : Fin d.dimension) (q : ℕ) :
    Fin (d.rowCount+1) → Fin d.dimension → ℤ :=
  Fin.lastCases (fun k => if k=j then (q:ℤ) else 0) d.coefficient
def fixedValue (d : Raw) (j : Fin d.dimension) (p q : ℕ) : Input :=
  pack (d.rowCount+1) d.dimension (fixedCoefficients d j q) (constants d p)

theorem fixed_feasible (d : Raw) (j : Fin d.dimension) (p q : ℕ) (hq : 0<q)
    (x : Fin d.dimension → ℚ) :
    Feasible (fixedValue d j p q).val x ↔ Feasible d x ∧ x j=(p:ℚ)/q := by
  have hq' : (q:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  change Feasible (pack (d.rowCount+1) d.dimension
    (fixedCoefficients d j q) (constants d p)).val x ↔ _
  rw [pack_feasible]
  constructor
  · rintro ⟨he,hb⟩
    have ho (i : Fin d.rowCount) := he i.castSucc
    have hn := he (Fin.last d.rowCount)
    simp only [fixedCoefficients,constants,Fin.lastCases_last,Fin.lastCases_castSucc] at ho hn
    have hj : (q:ℚ)*x j=p := by simpa using hn
    exact ⟨⟨ho,hb⟩,(eq_div_iff hq').mpr (by simpa [mul_comm] using hj)⟩
  · rintro ⟨⟨ho,hb⟩,hj⟩
    refine ⟨fun i => Fin.lastCases ?_ (fun i => ?_) i,hb⟩
    · have he : (q : ℚ) * x j = (p : ℚ) := by
        simpa only [mul_comm] using (eq_div_iff hq').mp hj
      simpa [fixedCoefficients,constants] using he
    · simpa [fixedCoefficients,constants] using ho i

end Threshold
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
