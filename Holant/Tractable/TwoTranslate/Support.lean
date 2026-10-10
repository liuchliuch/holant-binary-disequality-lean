import Holant.Tractable.AffinePhaseCriterion

namespace Holant.Tractable
noncomputable section
namespace TwoTranslate
open AffinePhase
variable {n : ℕ}


/-- A binary linear functional evaluated on a Boolean word. -/
def rowDot (a : Fin n → ZMod 2) (x : Word n) : ZMod 2 :=
  ∑ j, a j * bitValue (ZMod 2) (x j)

@[simp] theorem bitValue_xor (a b : Bool) :
    bitValue (ZMod 2) (Bool.xor a b) = bitValue (ZMod 2) a + bitValue (ZMod 2) b := by
  cases a <;> cases b <;> decide

@[simp] theorem rowDot_xor (a : Fin n → ZMod 2) (x y : Word n) :
    rowDot a (xor x y) = rowDot a x + rowDot a y := by
  simp [rowDot, mul_add, Finset.sum_add_distrib]

@[simp] theorem rowDot_origin (a : Fin n → ZMod 2) : rowDot a (origin n) = 0 := by
  simp [rowDot, origin]

/-- Binary residues are represented by their unique Boolean bit. -/
def residueBit (a : ZMod 2) : Bool := decide (a = 1)

@[simp] theorem bitValue_residueBit (a : ZMod 2) :
    bitValue (ZMod 2) (residueBit a) = a := by
  fin_cases a
  · change bitValue (ZMod 2) (residueBit 0) = 0
    decide
  · change bitValue (ZMod 2) (residueBit 1) = 1
    decide

theorem bitValue_injective : Function.Injective (bitValue (ZMod 2)) := by
  intro a b h
  cases a <;> cases b <;> simp_all

@[simp] theorem residueBit_add (a b : ZMod 2) :
    residueBit (a + b) = Bool.xor (residueBit a) (residueBit b) := by
  apply bitValue_injective
  simp

@[simp] theorem residueBit_zero : residueBit 0 = false := by decide
@[simp] theorem residueBit_one : residueBit 1 = true := by decide

/-- Translation by a kernel vector preserves every equation. -/
theorem holds_translate_iff (S : AffineSystem n) (w x : Word n)
    (hw : ∀ r, rowDot (S.matrix r) w = 0) :
    S.Holds (xor x w) ↔ S.Holds x := by
  change (∀ r, rowDot (S.matrix r) (xor x w) = S.rhs r) ↔
    (∀ r, rowDot (S.matrix r) x = S.rhs r)
  simp only [rowDot_xor, hw, add_zero]

/-- A row detecting the translation supplies the canonical selector. -/
def selector (S : AffineSystem n) (r : Fin S.rows) (x : Word n) : Bool :=
  residueBit (rowDot (S.matrix r) x + S.rhs r)

/-- Select the member of a translation pair that satisfies the detecting row. -/
def projection (S : AffineSystem n) (w : Word n) (r : Fin S.rows)
    (x : Word n) : Word n :=
  if selector S r x then xor x w else x

/-- Eliminate the detecting equation along the translation direction. -/
def saturationSystem (S : AffineSystem n) (w : Word n) (r : Fin S.rows) :
    AffineSystem n where
  rows := S.rows
  matrix k j := S.matrix k j + rowDot (S.matrix k) w * S.matrix r j
  rhs k := S.rhs k + rowDot (S.matrix k) w * S.rhs r

theorem rowDot_saturation (S : AffineSystem n) (w x : Word n) (r k : Fin S.rows) :
    rowDot ((saturationSystem S w r).matrix k) x =
      rowDot (S.matrix k) x + rowDot (S.matrix k) w * rowDot (S.matrix r) x := by
  simp [rowDot, saturationSystem, add_mul, mul_assoc, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem rowDot_projection (S : AffineSystem n) (w x : Word n) (r k : Fin S.rows) :
    rowDot (S.matrix k) (projection S w r x) = rowDot (S.matrix k) x +
      rowDot (S.matrix k) w * (rowDot (S.matrix r) x + S.rhs r) := by
  have hb := bitValue_residueBit (rowDot (S.matrix r) x + S.rhs r)
  change bitValue (ZMod 2) (selector S r x) = _ at hb
  cases h : selector S r x <;> simp only [h, bitValue_false, bitValue_true] at hb
  · simp [projection, h, ← hb]
  · simp [projection, h, ← hb]

theorem saturation_holds_projection (S : AffineSystem n) (w x : Word n)
    (r : Fin S.rows) :
    (saturationSystem S w r).Holds x ↔ S.Holds (projection S w r x) := by
  change (∀ k : Fin S.rows, rowDot ((saturationSystem S w r).matrix k) x =
    (saturationSystem S w r).rhs k) ↔
    (∀ k, rowDot (S.matrix k) (projection S w r x) = S.rhs k)
  simp only [rowDot_saturation, rowDot_projection]
  change (∀ k, rowDot (S.matrix k) x + rowDot (S.matrix k) w * rowDot (S.matrix r) x =
    S.rhs k + rowDot (S.matrix k) w * S.rhs r) ↔ _
  apply forall_congr'
  intro k
  rw [mul_add, ← add_assoc]
  constructor
  · intro h
    rw [h, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · intro h
    calc
      rowDot (S.matrix k) x + rowDot (S.matrix k) w * rowDot (S.matrix r) x =
          (rowDot (S.matrix k) x + rowDot (S.matrix k) w * rowDot (S.matrix r) x +
            rowDot (S.matrix k) w * S.rhs r) + rowDot (S.matrix k) w * S.rhs r := by
              rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = S.rhs k + rowDot (S.matrix k) w * S.rhs r := by rw [h]

theorem selector_of_holds (S : AffineSystem n) (x : Word n) (r : Fin S.rows)
    (hx : S.Holds x) : selector S r x = false := by
  have hr : rowDot (S.matrix r) x = S.rhs r := hx r
  simp [selector, hr, CharTwo.add_self_eq_zero]

@[simp] theorem projection_of_holds (S : AffineSystem n) (w x : Word n)
    (r : Fin S.rows) (hx : S.Holds x) : projection S w r x = x := by
  simp [projection, selector_of_holds S x r hx]

theorem selector_translate (S : AffineSystem n) (w x : Word n) (r : Fin S.rows)
    (hr : rowDot (S.matrix r) w = 1) :
    selector S r (xor x w) = !(selector S r x) := by
  simp only [selector, rowDot_xor, hr]
  have he : rowDot (S.matrix r) x + 1 + S.rhs r =
      (rowDot (S.matrix r) x + S.rhs r) + 1 := by ring
  rw [he, residueBit_add, residueBit_one]
  simp

theorem projection_translate (S : AffineSystem n) (w x : Word n) (r : Fin S.rows)
    (hr : rowDot (S.matrix r) w = 1) :
    projection S w r (xor x w) = projection S w r x := by
  simp only [projection, selector_translate S w x r hr]
  cases selector S r x <;> simp

theorem saturation_holds (S : AffineSystem n) (w x : Word n) (r : Fin S.rows)
    (hr : rowDot (S.matrix r) w = 1) :
    (saturationSystem S w r).Holds x ↔ S.Holds x ∨ S.Holds (xor x w) := by
  rw [saturation_holds_projection]
  constructor
  · intro h
    unfold projection at h
    cases hs : selector S r x <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (hx | hx)
    · simpa only [projection_of_holds S w x r hx] using hx
    · rw [← projection_translate S w x r hr, projection_of_holds S w (xor x w) r hx]
      exact hx

theorem holds_disjoint (S : AffineSystem n) (w x : Word n) (r : Fin S.rows)
    (hr : rowDot (S.matrix r) w = 1) : ¬(S.Holds x ∧ S.Holds (xor x w)) := by
  rintro ⟨hx, hxw⟩
  have ht := selector_translate S w x r hr
  rw [selector_of_holds S x r hx, selector_of_holds S (xor x w) r hxw] at ht
  contradiction

/-- Every binary residue is zero or one. -/
theorem residue_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A non-kernel direction has a row whose value is one. -/
theorem exists_detecting_row (S : AffineSystem n) (w : Word n)
    (hw : ¬ ∀ r, rowDot (S.matrix r) w = 0) :
    ∃ r, rowDot (S.matrix r) w = 1 := by
  push Not at hw
  obtain ⟨r, hr⟩ := hw
  exact ⟨r, (residue_eq_zero_or_one _).resolve_left hr⟩

theorem bitValue_projection (S : AffineSystem n) (w x : Word n)
    (r : Fin S.rows) (j : Fin n) :
    bitValue (ZMod 2) (projection S w r x j) = bitValue (ZMod 2) (x j) +
      bitValue (ZMod 2) (w j) * (rowDot (S.matrix r) x + S.rhs r) := by
  have hb := bitValue_residueBit (rowDot (S.matrix r) x + S.rhs r)
  change bitValue (ZMod 2) (selector S r x) = _ at hb
  cases h : selector S r x <;> simp only [h, bitValue_false, bitValue_true] at hb
  · simp [projection, h, ← hb]
  · simp [projection, h, ← hb]

/-- The chosen representative is an affine map of Boolean vector spaces. -/
theorem projection_affine (S : AffineSystem n) (w x y : Word n) (r : Fin S.rows) :
    projection S w r (xor x y) =
      xor (xor (projection S w r x) (projection S w r y))
        (projection S w r (origin n)) := by
  funext j
  apply bitValue_injective
  simp only [xor_apply, bitValue_xor, bitValue_projection, rowDot_xor,
    rowDot_origin, origin, bitValue_false, zero_add]
  ring_nf
  have h3 : (3 : ZMod 2) = 1 := by decide
  rw [h3, mul_one]

/-- On the union support exactly one term remains, at the affine projection. -/
theorem sum_eq_projected {R : Type*} [AddZeroClass R]
    (S : AffineSystem n) (w : Word n) (r : Fin S.rows)
    (hr : rowDot (S.matrix r) w = 1) (f : Word n → R)
    (hf : ∀ x, ¬ S.Holds x → f x = 0) (x : Word n) :
    f x + f (xor x w) =
      if (saturationSystem S w r).Holds x then f (projection S w r x) else 0 := by
  by_cases hx : S.Holds x
  · have hn : ¬ S.Holds (xor x w) := fun hh => holds_disjoint S w x r hr ⟨hx, hh⟩
    have hu := (saturation_holds S w x r hr).mpr (Or.inl hx)
    simp [hu, hf _ hn, projection_of_holds S w x r hx]
  · by_cases hxw : S.Holds (xor x w)
    · have hu := (saturation_holds S w x r hr).mpr (Or.inr hxw)
      have hp : projection S w r x = xor x w := by
        rw [← projection_translate S w x r hr, projection_of_holds S w (xor x w) r hxw]
      simp [hu, hf _ hx, hp]
    · have hu : ¬ (saturationSystem S w r).Holds x := by
        rw [saturation_holds S w x r hr]
        exact not_or.mpr ⟨hx, hxw⟩
      simp [hu, hf _ hx, hf _ hxw]

/-- Projection always chooses one of the original two arguments. -/
theorem projection_mem_pair (S : AffineSystem n) (w x : Word n) (r : Fin S.rows) :
    projection S w r x = x ∨ projection S w r x = xor x w := by
  unfold projection
  cases selector S r x <;> simp

/-- The affine formula on a disjoint translate union has the projected phase. -/
theorem formula_sum_eq_projected (S : AffineSystem n) (w : Word n) (r : Fin S.rows)
    (hr : rowDot (S.matrix r) w = 1) (s : AlgebraicComplex) (Q : QuadraticPhase n)
    (x : Word n) :
    affineFormula s S Q x + affineFormula s S Q (xor x w) =
      if (saturationSystem S w r).Holds x then
        s * fourthRootPhase (Q.eval (projection S w r x)) else 0 := by
  rw [sum_eq_projected S w r hr (affineFormula s S Q)
    (fun y hy => by simp [affineFormula, hy]) x]
  by_cases hu : (saturationSystem S w r).Holds x
  · have hp := (saturation_holds_projection S w x r).mp hu
    simp [hu, affineFormula, hp]
  · simp [hu]

end TwoTranslate

namespace AffineSystem

/-- Stack two systems without changing either set of equations. -/
def inter {n : ℕ} (S T : AffineSystem n) : AffineSystem n where
  rows := S.rows + T.rows
  matrix := Fin.addCases S.matrix T.matrix
  rhs := Fin.addCases S.rhs T.rhs

@[simp] theorem inter_holds {n : ℕ} (S T : AffineSystem n) (x : Fin n → Bool) :
    (inter S T).Holds x ↔ S.Holds x ∧ T.Holds x := by
  constructor
  · intro h
    constructor
    · intro r
      simpa [inter] using h (Fin.castAdd T.rows r)
    · intro r
      simpa [inter] using h (Fin.natAdd S.rows r)
  · rintro ⟨hS, hT⟩ r
    refine Fin.addCases ?_ ?_ r
    · intro k
      simpa [inter] using hS k
    · intro k
      simpa [inter] using hT k

end AffineSystem

/-- Restricting an affine signature to another affine system preserves affinity. -/
theorem Affine.restrict {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f)
    (U : AffineSystem n) : Affine (fun x => if U.Holds x then f x else 0) := by
  rcases hf with rfl | ⟨s, hs, S, Q, rfl⟩
  · left
    funext x
    simp
  · right
    refine ⟨s, hs, S.inter U, Q, ?_⟩
    funext x
    by_cases hS : S.Holds x <;> by_cases hU : U.Holds x <;>
      simp [affineFormula, hS, hU]

end
end Holant.Tractable
