import Holant.ReedMuller.LowArity.Checker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace Holant.ReedMuller.LowArity
open scoped BigOperators

abbrev BinaryVector (n : ℕ) := Fin n → ZMod 2
abbrev BinaryCode (n : ℕ) := Submodule (ZMod 2) (BinaryVector n)

def dot {n : ℕ} (x y : BinaryVector n) : ZMod 2 := ∑ i, x i * y i

def SelfDual {n : ℕ} (D : BinaryCode n) : Prop :=
  ∀ x, x ∈ D ↔ ∀ y, y ∈ D → dot x y = 0

abbrev Matching (r n : ℕ) := (Fin r × Fin 2) ≃ Fin n

def Matching.Holds {r n : ℕ} (M : Matching r n) (x : BinaryVector n) : Prop :=
  ∀ e, x (M (e,0)) = x (M (e,1))

instance {r n : ℕ} (M : Matching r n) (x : BinaryVector n) : Decidable (M.Holds x) := by
  unfold Matching.Holds
  infer_instance

def orth {n : ℕ} (x y : BinaryVector n) : Bool := decide (dot x y = 0)

def bits (n k : ℕ) : BinaryVector n := fun i => if k.testBit i.val then 1 else 0

/-- The checker uses only self-orthogonality; the exact converse is supplied
by the mathematical self-duality hypothesis. -/
theorem selfDual_eq_matching {r n m : ℕ} (models : Fin m → Matching r n)
    (hmodel : ∀ a x y, (models a).Holds x → (models a).Holds y → dot x y = 0)
    (T : Certificate (BinaryVector n) (Fin m))
    (hcheck : check orth (fun a x => decide ((models a).Holds x))
      (Finset.univ.filter fun x => orth x x) T = true)
    (D : BinaryCode n) (hD : SelfDual D) :
    ∃ a, ∀ x, x ∈ D ↔ (models a).Holds x := by
  obtain ⟨a,ha⟩ := check_sound orth (fun a x => decide ((models a).Holds x)) T _ hcheck
    (fun x => x ∈ D)
    (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      simp only [orth,decide_eq_true_eq]
      exact (hD x).mp hx x hx⟩)
    (fun x hx y hy => by
      simp only [orth,decide_eq_true_eq]
      exact (hD x).mp hx y hy)
  simp only [decide_eq_true_eq] at ha
  refine ⟨a,fun x => ⟨ha x,?_⟩⟩
  intro hx
  apply (hD x).mpr
  intro y hy
  exact hmodel a x y hx (ha y hy)

end Holant.ReedMuller.LowArity
