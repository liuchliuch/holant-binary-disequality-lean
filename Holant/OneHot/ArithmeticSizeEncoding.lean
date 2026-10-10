import Holant.OneHot.ArithmeticSizeGraph
import Holant.Complexity.EncodedHolantOutputSize

/-!
# Faithfully encoded intermediate values of one-hot arithmetic programs

The fixed coefficient family is extended by the fixed field unit for padding.
All actual executed operands/results, and all returned values, have explicitly
linear binary length bounds in the structural input size. This closes the value
size obligation, not effective graph preprocessing or field-arithmetic bit time.
-/

namespace Holant.OneHot.ArithmeticSize

variable {K A : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
variable (F : Algebraic.FixedField K n) (coeff : A → Fin n → ℚ)

/-- Padding adds one fixed field coefficient, independent of the instance. -/
def withUnit : Option A → Fin n → ℚ
  | none => F.unitCode
  | some a => coeff a

@[simp] theorem decode_withUnit_none : F.decode (withUnit F coeff none) = 1 := F.decode_unit

/-- Every original family member has a one-factor expansion in the enlarged
fixed family. This is the only hypothesis needed for literal input coefficients. -/
theorem family_bound {x : K} (hx : ∃ a, x = F.decode (coeff a)) :
    Bound (fun a => F.decode (withUnit F coeff a)) 1 x := by
  rcases hx with ⟨a, rfl⟩
  exact Bound.coefficient (some a)

variable [Fintype A]

/-- The actual canonical binary encoding of every tree-program operand/result
is bounded linearly in the represented vertices plus edges. -/
theorem tree_values_encoded_length_le (t : Tree K)
    (h : t.All (fun x => ∃ a, x = F.decode (coeff a)))
    (x : K) (hx : x ∈ t.program.values) :
    (F.encoding.encode x).length ≤ bitBound F (withUnit F coeff) (treeBudget t) := by
  have hb := tree_program_bound none (decode_withUnit_none F coeff) t
    (Tree.All.mono t h (fun _ hx => family_bound F coeff hx))
  exact (hb.2.2 x hx).encoded_length_le F (withUnit F coeff)

/-- Both returned boundary messages satisfy the same faithful length bound. -/
theorem tree_results_encoded_length_le (t : Tree K)
    (h : t.All (fun x => ∃ a, x = F.decode (coeff a))) :
    (F.encoding.encode t.program.run.1.1).length ≤ bitBound F (withUnit F coeff) (treeBudget t) ∧
    (F.encoding.encode t.program.run.1.2).length ≤ bitBound F (withUnit F coeff) (treeBudget t) := by
  have hb := tree_program_bound none (decode_withUnit_none F coeff) t
    (Tree.All.mono t h (fun _ hx => family_bound F coeff hx))
  simpa only [Tree.program_run] using And.intro
    (hb.1.encoded_length_le F (withUnit F coeff))
    (hb.2.1.encoded_length_le F (withUnit F coeff))

/-- Forest partial products and sums are included, including empty forests. -/
theorem forest_values_encoded_length_le (ts : Forest K)
    (h : ts.All (fun x => ∃ a, x = F.decode (coeff a)))
    (x : K) (hx : x ∈ ts.program.values) :
    (F.encoding.encode x).length ≤ bitBound F (withUnit F coeff) (forestBudget ts) := by
  have hb := forest_program_bound none (decode_withUnit_none F coeff) ts
    (Forest.All.mono ts h (fun _ hx => family_bound F coeff hx))
  exact (hb.2.2 x hx).encoded_length_le F (withUnit F coeff)

/-- No virtual-parent value is needed for the genuine closed-root program. -/
theorem closed_values_encoded_length_le (ts : Forest K) (a : K)
    (h : ts.All (fun x => ∃ a, x = F.decode (coeff a)))
    (ha : ∃ j, a = F.decode (coeff j))
    (x : K) (hx : x ∈ (ts.closedProgram a).values) :
    (F.encoding.encode x).length ≤ bitBound F (withUnit F coeff) (forestBudget ts + 2) := by
  have hb := closed_program_bound none (decode_withUnit_none F coeff) ts a
    (Forest.All.mono ts h (fun _ hx => family_bound F coeff hx)) (family_bound F coeff ha)
  exact (hb.2 x hx).encoded_length_le F (withUnit F coeff)

/-- Final closed-root return value, paired with the separate trace result above. -/
theorem closed_result_encoded_length_le (ts : Forest K) (a : K)
    (h : ts.All (fun x => ∃ a, x = F.decode (coeff a)))
    (ha : ∃ j, a = F.decode (coeff j)) :
    (F.encoding.encode (ts.closedProgram a).run.1).length ≤
      bitBound F (withUnit F coeff) (forestBudget ts + 2) := by
  have hb := closed_program_bound none (decode_withUnit_none F coeff) ts a
    (Forest.All.mono ts h (fun _ hx => family_bound F coeff hx)) (family_bound F coeff ha)
  exact hb.1.encoded_length_le F (withUnit F coeff)

/-- Explicit affine dependence of the binary length bound on its size parameter.
All constants here depend only on the fixed field presentation/coefficient family. -/
theorem bitBound_affine (b : ℕ) :
    bitBound F coeff b =
      n * (4 * (1 + (n * n * F.toArithmeticData.familyBound coeff *
        F.toArithmeticData.familyBound coeff).size +
        2 * (F.toArithmeticData.familyDenominator coeff).size)) * b +
      n * (4 * ((F.toArithmeticData.familyBound coeff).size +
        (F.toArithmeticData.familyDenominator coeff).size + 3) + 1) := by
  unfold bitBound
  ring

/-- Increasing the structural budget preserves the explicit binary-length bound. -/
theorem bitBound_mono {b c : ℕ} (h : b ≤ c) : bitBound F coeff b ≤ bitBound F coeff c := by
  rw [bitBound_affine, bitBound_affine]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

end Holant.OneHot.ArithmeticSize

namespace Holant.Network

open OneHot OneHot.ArithmeticSize

variable {K A : Type*} [Field K] [Algebra ℚ K] {n : ℕ} [Fintype A]
variable (F : Algebraic.FixedField K n) (coeff : A → Fin n → ℚ) (N : Network K 0)

/-- Every actual arithmetic operand/result, plus the final return value, has
linear faithful binary length in the ORIGINAL graph's vertex count. This is
stronger than a bound only on the final denotation and does not infer value size
from the number of arithmetic instructions. -/
theorem oneHotProgram_encoded_length_le
    (h : ∀ v x, ∃ a, N.vertex v x = F.decode (coeff a)) :
    (F.encoding.encode N.oneHotProgram.run.1).length ≤
      bitBound F (withUnit F coeff) (5 * N.shape.vertices) ∧
    ∀ x ∈ N.oneHotProgram.values, (F.encoding.encode x).length ≤
      bitBound F (withUnit F coeff) (5 * N.shape.vertices) := by
  have hb := N.oneHotProgram_bound none (decode_withUnit_none F coeff)
    (fun v x => family_bound F coeff (h v x))
  exact ⟨hb.1.encoded_length_le F (withUnit F coeff),
    fun x hx => (hb.2 x hx).encoded_length_le F (withUnit F coeff)⟩

end Holant.Network

namespace Holant.Complexity.ExactSignatureTables

open OneHot OneHot.ArithmeticSize

variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}
variable (F : Algebraic.FixedField K n) (T : ExactSignatureTables n s b arity)

/-- Execute the existing arbitrary-graph arithmetic program on the literally
parsed fixed-table network. This does not claim effective extraction. -/
noncomputable def oneHotArithmeticProgram (r : Input s b arity) : Arithmetic K K :=
  ((familyNetwork r).realize F T.coefficient).oneHotProgram

/-- One explicit polynomial for every operand/result of the parsed program.
The degree is at most one; all its constants are fixed before the input arrives. -/
noncomputable def oneHotIntermediatePolynomial : Polynomial ℕ :=
  let C := withUnit F T.coefficient
  let M := F.toArithmeticData.familyBound C
  let D := F.toArithmeticData.familyDenominator C
  Polynomial.C (n * (4 * (1 + (n * n * M * M).size + 2 * D.size)) * 5) * Polynomial.X +
    Polynomial.C (n * (4 * (M.size + D.size + 3) + 1))

theorem oneHotIntermediatePolynomial_eval (m : ℕ) :
    (T.oneHotIntermediatePolynomial F).eval m =
      bitBound F (withUnit F T.coefficient) (5 * m) := by
  rw [bitBound_affine]
  simp only [oneHotIntermediatePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- Polynomial bounds in the ACTUAL serialized input length, simultaneously
for the returned value and every executed arithmetic operand/result. No bound
on arithmetic bit time is assumed or asserted. -/
theorem oneHotArithmeticProgram_encoded_length_le (r : Input s b arity) :
    (F.encoding.encode (T.oneHotArithmeticProgram F r).run.1).length ≤
      (T.oneHotIntermediatePolynomial F).eval
        ((RawClosedNetwork.validatedEncoding s b arity).encode r).length ∧
    ∀ x ∈ (T.oneHotArithmeticProgram F r).values,
      (F.encoding.encode x).length ≤ (T.oneHotIntermediatePolynomial F).eval
        ((RawClosedNetwork.validatedEncoding s b arity).encode r).length := by
  have hb := ((familyNetwork r).realize F T.coefficient).oneHotProgram_encoded_length_le
    F T.coefficient (fun v x => ⟨(familyNetwork r).vertexLabel v x, rfl⟩)
  have hsize := r.val.decoded_counts_le_input_length r.property
  have hv : ((familyNetwork r).realize F T.coefficient).shape.vertices ≤
      ((RawClosedNetwork.validatedEncoding s b arity).encode r).length := by
    change r.val.vertices.length ≤ _
    change r.val.vertices.length + r.val.edges.length ≤
      ((RawClosedNetwork.validatedEncoding s b arity).encode r).length at hsize
    omega
  have hbound := bitBound_mono F (withUnit F T.coefficient) (Nat.mul_le_mul_left 5 hv)
  rw [← T.oneHotIntermediatePolynomial_eval F
    ((RawClosedNetwork.validatedEncoding s b arity).encode r).length] at hbound
  exact ⟨hb.1.trans hbound, fun x hx => (hb.2 x hx).trans hbound⟩

end Holant.Complexity.ExactSignatureTables
