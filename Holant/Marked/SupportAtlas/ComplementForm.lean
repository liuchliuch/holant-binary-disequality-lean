import Holant.Marked.SupportAtlas.Dressing
import Holant.Projective.CyclicQuaternary.Coordinates

/-! Literal coefficient form of the marked support atlas after a physical bit dressing. -/
noncomputable section
namespace Holant.Marked.SupportAtlas
open Holant.Tractable
open Holant.Projective.CyclicQuaternary

/-- A delta tensor at an exact ordered four-port word. -/
def atom (w : Word) : Signature Scalar 4 := fun x => if x = w then 1 else 0

def pairWord (i : Fin 3) : Word := Holant.Projective.CyclicQuaternary.join i false true true false false

/-- The source's three complementary weight-two blocks, with their inherited order. -/
def complementExpression (a h : Scalar) (K : Finset (Fin 3)) (b d : Fin 3 → Scalar) :
    Signature Scalar 4 := a • atom (fun _ => false) + h • atom (fun _ => true) +
      ∑ i ∈ K, (b i • atom (pairWord i) + d i • atom (complement (pairWord i)))

def ComplementForm (g : Signature Scalar 4) : Prop :=
  ∃ (a h : Scalar) (selected : Finset (Fin 3)) (b d : Fin 3 → Scalar),
    a ≠ 0 ∧ h ≠ 0 ∧ (∀ i ∈ selected, b i ≠ 0) ∧ (∀ i ∈ selected, d i ≠ 0) ∧
      g = complementExpression a h selected b d

@[simp] theorem zeroWord_eq : (![false,false,false,false] : Word) = (fun _ => false) := by
  funext i; fin_cases i <;> rfl
@[simp] theorem oneWord_eq : (![true,true,true,true] : Word) = (fun _ => true) := by
  funext i; fin_cases i <;> rfl

theorem coordinates_second (g : Signature Scalar 4) (i : Fin 3) :
    (coordinates g i).2 = g (complement (pairWord i)) := by
  change g (Holant.Projective.CyclicQuaternary.join i false false false true true) = _
  apply congrArg g
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem ofCoordinates_atoms (a h : Scalar) (xs : Blocks Scalar) :
    ofCoordinates a h xs = complementExpression a h Finset.univ
      (fun i => (xs i).1) (fun i => (xs i).2) := by
  funext x
  have hx : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [ofCoordinates, complementExpression, atom, pairWord, complement,
      Holant.Projective.CyclicQuaternary.join, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

theorem complementForm_of_even {g : Signature Scalar 4} (heven : EvenSupported g)
    (hzero : g (fun _ => false) ≠ 0) (hone : g (fun _ => true) ≠ 0)
    (hcomp : ∀ w, g (complement w) = 0 ↔ g w = 0) : ComplementForm g := by
  let xs := coordinates g
  let K : Finset (Fin 3) := Finset.univ.filter fun i => (xs i).1 ≠ 0
  have hc (i : Fin 3) : (xs i).2 = 0 ↔ (xs i).1 = 0 := by
    have hh := hcomp (pairWord i)
    change (coordinates g i).2 = 0 ↔ (coordinates g i).1 = 0
    rw [coordinates_second]
    exact hh
  have he : complementExpression (endpoint0 g) (endpoint1 g) Finset.univ
      (fun i => (xs i).1) (fun i => (xs i).2) =
      complementExpression (endpoint0 g) (endpoint1 g) K
        (fun i => (xs i).1) (fun i => (xs i).2) := by
    unfold complementExpression
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz : (xs i).1 = 0
    · simp [hz, (hc i).mpr hz]
    · simp [hz]
  refine ⟨endpoint0 g, endpoint1 g, K, (fun i => (xs i).1), (fun i => (xs i).2),
    (by simpa [endpoint0] using hzero), (by simpa [endpoint1] using hone), ?_, ?_, ?_⟩
  · intro i hi; exact (Finset.mem_filter.mp hi).2
  · intro i hi; exact (hc i).not.mpr (Finset.mem_filter.mp hi).2
  · exact (ofCoordinates_extract g heven).symm.trans ((ofCoordinates_atoms _ _ _).trans he)

@[simp] theorem xorWord_zero (mask : Word) : xorWord (fun _ => false) mask = mask := by
  funext i; simp [xorWord]
@[simp] theorem xorWord_one (mask : Word) : xorWord (fun _ => true) mask = complement mask := by
  funext i; simp [xorWord, complement]

theorem parity_xorWord (x y : Word) : parity (xorWord x y) = (parity x ^^ parity y) := by
  simp only [parity, xorWord]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;> rfl

theorem xorWord_complement (x y : Word) : xorWord (complement x) y = complement (xorWord x y) := by
  funext i
  change ((!(x i)) ^^ y i) = !(x i ^^ y i)
  cases x i <;> cases y i <;> rfl

theorem odd_eq_parity (x : Word) : odd x = parity x := by
  simp [odd, parity, Bool.xor_assoc]

end Holant.Marked.SupportAtlas
