import Holant.Complexity.ClosedNetworkSemantics
import Holant.Algebraic.NetworkOutputSize
import Holant.Complexity.OutputSize

/-!
# Polynomial bit-length of faithfully encoded fixed-field Holant answers

This combines an actual framed, validated closed-instance encoding with the exact
ordered-port semantics and the general fixed-field coordinate-growth theorem.
Vertex and edge records occupy bits even when their labels or arities are zero.
No polynomial evaluation-time claim is inferred from this output-size result.
-/

namespace Holant.Complexity

open Computability Holant.Algebraic

/-- Exact rational-coordinate signature tables, fixed independently of instances. -/
structure ExactSignatureTables (n s b : ℕ) (arity : ℕ → ℕ) where
  vertex : (i : Fin s) → Holant.Signature (Fin n → ℚ) (arity i.val)
  edge : Fin b → Bool → Bool → (Fin n → ℚ)

namespace ExactSignatureTables

variable {n s b : ℕ} {arity : ℕ → ℕ}

/-- Every table entry is one member of a single fixed finite coefficient family. -/
abbrev CoefficientIndex (s b : ℕ) (arity : ℕ → ℕ) :=
  (Σ i : Fin s, (Fin (arity i.val) → Bool)) ⊕ (Fin b × Bool × Bool)

def coefficient (T : ExactSignatureTables n s b arity) : CoefficientIndex s b arity → (Fin n → ℚ)
  | .inl ⟨i, x⟩ => T.vertex i x
  | .inr (i, x, y) => T.edge i x y

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  { r : RawClosedNetwork // r.WellFormed s b arity }

/-- The decoded shape and every fixed table label are preserved literally. -/
noncomputable def familyNetwork (r : Input s b arity) :
    FixedField.FamilyNetwork (A := CoefficientIndex s b arity) 0 where
  shape := r.val.shape r.property
  vertexLabel v x := .inl ⟨r.val.signatureLabel r.property v, x⟩
  edgeLabel e x y := .inr (r.val.edgeLabel r.property e, x, y)

/-- The semantic Holant function of the actual validated input data. -/
noncomputable def evaluate {K : Type} [Field K] [Algebra ℚ K]
    (F : FixedField K n) (T : ExactSignatureTables n s b arity) (r : Input s b arity) : K :=
  ((familyNetwork r).realize F T.coefficient).denote Fin.elim0

/-- This is exactly the parsed network with the stated signature and edge tables,
not a replacement problem chosen just to have a size bound. -/
theorem evaluate_eq_decoded {K : Type} [Field K] [Algebra ℚ K]
    (F : FixedField K n) (T : ExactSignatureTables n s b arity) (r : Input s b arity) :
    T.evaluate F r = (r.val.realize r.property
      (fun i x => F.decode (T.vertex i x)) (fun i x y => F.decode (T.edge i x y))).denote Fin.elim0 :=
  rfl

/-- An explicit natural-coefficient polynomial in the actual input bit length. -/
noncomputable def outputPolynomial {K : Type} [Field K] [Algebra ℚ K]
    (F : FixedField K n) (T : ExactSignatureTables n s b arity) : Polynomial ℕ :=
  let M := F.toArithmeticData.familyBound T.coefficient
  let D := F.toArithmeticData.familyDenominator T.coefficient
  Polynomial.C n * (Polynomial.C 4 *
    (Polynomial.C 2 * Polynomial.X + Polynomial.C M.size +
      Polynomial.X * Polynomial.C (n * n * M * M).size +
      (Polynomial.C 2 * Polynomial.X + 1) * Polynomial.C D.size + Polynomial.C 3) + 1)

/-- Full output-size bridge from serialized graph bits to exact field-answer bits. -/
theorem output_length_le {K : Type} [Field K] [Algebra ℚ K]
    (F : FixedField K n) (T : ExactSignatureTables n s b arity) (r : Input s b arity) :
    (F.encoding.encode (T.evaluate F r)).length ≤
      (T.outputPolynomial F).eval ((RawClosedNetwork.validatedEncoding s b arity).encode r).length := by
  have h := (familyNetwork r).output_length_le F T.coefficient Fin.elim0
  have hsize := r.val.decoded_counts_le_input_length r.property
  change r.val.vertices.length + r.val.edges.length ≤
    ((RawClosedNetwork.validatedEncoding s b arity).encode r).length at hsize
  apply le_trans h
  simp only [outputPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  change n * (4 * (2 * r.val.edges.length + (F.toArithmeticData.familyBound T.coefficient).size +
      (r.val.vertices.length + r.val.edges.length) *
        (n * n * F.toArithmeticData.familyBound T.coefficient * F.toArithmeticData.familyBound T.coefficient).size +
      (2 * (r.val.vertices.length + r.val.edges.length) + 1) *
        (F.toArithmeticData.familyDenominator T.coefficient).size + 3) + 1) ≤ _
  apply Nat.mul_le_mul_left
  have he : r.val.edges.length ≤
      ((RawClosedNetwork.validatedEncoding s b arity).encode r).length := by omega
  have h1 := Nat.mul_le_mul_right
    (n * n * F.toArithmeticData.familyBound T.coefficient * F.toArithmeticData.familyBound T.coefficient).size hsize
  have h2 := Nat.mul_le_mul_right (F.toArithmeticData.familyDenominator T.coefficient).size
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsize) 1)
  omega

/-- The actual Holant function now has a polynomial encoded-answer bound suitable
for the controlled function-oracle interface. -/
noncomputable def outputBound {K : Type} [Field K] [Algebra ℚ K]
    (F : FixedField K n) (T : ExactSignatureTables n s b arity) :
    PolynomialOutputBound (RawClosedNetwork.validatedEncoding s b arity) F.encoding (T.evaluate F) where
  bound := T.outputPolynomial F
  length_le := T.output_length_le F

end ExactSignatureTables
end Holant.Complexity
