import Holant.ReedMuller.FlatNetwork.Projection
import Mathlib.Analysis.Complex.Basic

/-! Exact affine contraction fibres over F2. A feasible boundary has either
one or two internal lifts, uniformly; the actual scalar is retained. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def lift (eta b : ZMod 2) (x : BinaryVector n) : BinaryVector (n+2) := Fin.cons b (Fin.cons (b+eta) x)
def flatValue (c : ℂ) (a : BinaryVector n) (D : BinaryCode n) : BinaryVector n → ℂ :=
  fun x => if x-a∈D then c else 0

def closeValue (eta : ZMod 2) (f : BinaryVector (n+2) → ℂ) : BinaryVector n → ℂ :=
  fun x => ∑ b : ZMod 2,f (lift eta b x)

def fiberMultiplier (D : BinaryCode (n+2)) : ℂ := if pairWord n∈D then 2 else 1

theorem fiberMultiplier_nonzero (D : BinaryCode (n+2)) : fiberMultiplier D≠0 := by
  unfold fiberMultiplier
  split <;> norm_num

theorem prepend_difference (a b : ZMod 2) (x : BinaryVector n) :
    prepend b x-prepend a x=(b-a) • pairWord n := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [prepend,pairWord]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [prepend,pairWord]
    · simp [prepend,pairWord]

theorem sub_eq_one_of_ne (a b : ZMod 2) (h : a≠b) : a-b=1 := by
  have H : ∀ a b : ZMod 2,a≠b → a-b=1 := by decide
  exact H a b h

theorem prepend_mem_iff (D : BinaryCode (n+2)) (x : BinaryVector n) (a : ZMod 2)
    (ha : prepend a x∈D) (b : ZMod 2) :
    prepend b x∈D ↔ b=a ∨ pairWord n∈D := by
  by_cases hb : b=a
  · subst b
    simp [ha]
  · have he : prepend b x-prepend a x=pairWord n := by
      rw [prepend_difference,sub_eq_one_of_ne _ _ hb,one_smul]
    constructor
    · intro h
      exact Or.inr (he ▸ D.sub_mem h ha)
    · rintro (h|h)
      · exact False.elim (hb h)
      · have H := D.add_mem h ha
        rw [←he,sub_add_cancel] at H
        exact H

theorem indicator_fiber_sum (D : BinaryCode (n+2)) (x : BinaryVector n) :
    (∑ b : ZMod 2,if prepend b x∈D then (1:ℂ) else 0)=
      if x∈equalProjection D then fiberMultiplier D else 0 := by
  classical
  by_cases hx : x∈equalProjection D
  · obtain ⟨a,ha⟩ := hx
    rw [if_pos (show x∈equalProjection D from ⟨a,ha⟩)]
    simp_rw [prepend_mem_iff D x a ha]
    by_cases hd : pairWord n∈D
    · simp [hd,fiberMultiplier]
    · simp [hd,fiberMultiplier]
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro b _
    have hb : prepend b x∉D := fun h => hx ⟨b,h⟩
    simp [hb]

theorem lift_affine_difference (eta b b0 : ZMod 2) (x x0 : BinaryVector n)
    (a : BinaryVector (n+2)) :
    lift eta b x-a=prepend (b-b0) (x-x0)+(lift eta b0 x0-a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [lift,prepend]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [lift,prepend]
      ring
    · simp [lift,prepend]

theorem lift_mem_translate (D : BinaryCode (n+2)) (a : BinaryVector (n+2))
    (eta b0 : ZMod 2) (x0 : BinaryVector n) (h0 : lift eta b0 x0-a∈D)
    (b : ZMod 2) (x : BinaryVector n) :
    lift eta b x-a∈D ↔ prepend (b-b0) (x-x0)∈D := by
  rw [lift_affine_difference eta b b0 x x0 a]
  constructor
  · intro h
    have H := D.sub_mem h h0
    simpa using H
  · intro h
    exact D.add_mem h h0

theorem close_flat_feasible (D : BinaryCode (n+2)) (a : BinaryVector (n+2)) (c : ℂ)
    (eta b0 : ZMod 2) (x0 : BinaryVector n) (h0 : lift eta b0 x0-a∈D) :
    closeValue eta (flatValue c a D)=flatValue (c*fiberMultiplier D) x0 (equalProjection D) := by
  funext x
  simp only [closeValue,flatValue,lift_mem_translate D a eta b0 x0 h0]
  have H := (Equiv.subRight b0).sum_comp
    (fun b : ZMod 2 => if prepend b (x-x0)∈D then c else 0)
  change (∑ b : ZMod 2,if prepend (b-b0) (x-x0)∈D then c else 0)=
    ∑ b : ZMod 2,if prepend b (x-x0)∈D then c else 0 at H
  rw [H]
  have he : (∑ b : ZMod 2,if prepend b (x-x0)∈D then c else 0)=
      c*∑ b : ZMod 2,if prepend b (x-x0)∈D then (1:ℂ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split <;> simp
  rw [he,indicator_fiber_sum]
  split <;> simp_all

/-- The complete local affine/self-dual closure, with empty support and the
explicit nonzero fibre multiplier, including a closed nullary output. -/
theorem close_flat_selfDual (D : BinaryCode (n+2)) (hD : SelfDual D)
    (a : BinaryVector (n+2)) (c : ℂ) (hc : c≠0) (eta : ZMod 2) :
    closeValue eta (flatValue c a D)=0 ∨
      ∃ x0 : BinaryVector n,
        closeValue eta (flatValue c a D)=flatValue (c*fiberMultiplier D) x0 (equalProjection D) ∧
        c*fiberMultiplier D≠0 ∧ SelfDual (equalProjection D) := by
  classical
  by_cases he : ∃ b x,lift eta b x-a∈D
  · obtain ⟨b,x,hx⟩ := he
    exact Or.inr ⟨x,close_flat_feasible D a c eta b x hx,
      mul_ne_zero hc (fiberMultiplier_nonzero D),equalProjection_selfDual D hD⟩
  · left
    funext x
    apply Finset.sum_eq_zero
    intro b _
    have hn : lift eta b x-a∉D := fun h => he ⟨b,x,h⟩
    simp [flatValue,hn]

end
end Holant.ReedMuller.FlatNetwork
