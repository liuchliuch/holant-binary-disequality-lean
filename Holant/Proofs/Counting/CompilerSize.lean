import Holant.Proofs.Counting.RawCompiler
import Holant.Complexity.FixedGadgetSubstitution.Size
import Mathlib.Tactic.IntervalCases


namespace Holant.LocalDrafts.CountingHardness.RawCompiler

open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution

def vertexAdds {n : ℕ} : Circuit n → ℕ
  | .output _ => 0
  | .constant _ c => 2 + vertexAdds c
  | .nand _ _ c => 4 + vertexAdds c

theorem rows_length {n : ℕ} (c : Circuit n) (env : Fin n → RawEndpoint) (offset : ℕ) :
    (rows c env offset).length = n + vertexAdds c := by
  induction c generalizing offset with
  | output out => simp [rows, vertexAdds]
  | constant b c ih => simp [rows, vertexAdds, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
  | nand a b c ih => simp [rows, vertexAdds, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

theorem freshEdges_le {n : ℕ} (c : Circuit n) : freshEdges c ≤ 5 * c.gates := by
  induction c with
  | output out => simp [freshEdges, Circuit.gates]
  | constant b c ih => simp only [freshEdges, Circuit.gates]; omega
  | nand a b c ih => simp only [freshEdges, Circuit.gates]; omega

theorem vertexAdds_le {n : ℕ} (c : Circuit n) : vertexAdds c ≤ 4 * c.gates := by
  induction c with
  | output out => simp [vertexAdds, Circuit.gates]
  | constant b c ih => simp only [vertexAdds, Circuit.gates]; omega
  | nand a b c ih => simp only [vertexAdds, Circuit.gates]; omega

theorem compile_counts (c : CircuitInstance) :
    (compile c).vertices.length ≤ 6 * (CircuitInstance.encoding.encode c).length ∧
    (compile c).edges.length ≤ 6 * (CircuitInstance.encoding.encode c).length := by
  have hi := c.inputs_le_encoded_length
  have hg := c.gates_le_encoded_length
  have hv := vertexAdds_le c.circuit
  have he := freshEdges_le c.circuit
  simp only [compile, List.length_append, List.length_ofFn, rows_length, List.length_replicate]
  constructor <;> omega

/-- Coarse quadratic output bound, obtained from the existing faithful codec.
It includes endpoints, labels, delimiters, and all unused input vertices. -/
theorem compile_encoded_length (c : CircuitInstance) :
    (RawClosedNetwork.encoding.encode (compile c)).length ≤
      2500 * ((CircuitInstance.encoding.encode c).length + 1) ^ 2 := by
  have hraw := raw_length_le (compile c) (compile_wellFormed c) 3 (by
    intro i hi
    interval_cases i <;> simp [GateAlphabet.arity])
  have hv := (compile_counts c).1
  have he := (compile_counts c).2
  have hprod := Nat.mul_le_mul he hv
  nlinarith

end Holant.LocalDrafts.CountingHardness.RawCompiler

namespace Holant.LocalDrafts.CountingHardness.CircuitInstance

open Computability Holant.Complexity

theorem value_le (c : CircuitInstance) : c.value ≤ 2 ^ c.inputs := by
  simpa [value] using countAccepted_le c.circuit.eval

theorem output_length_le (c : CircuitInstance) :
    (encodingNatBool.encode c.value).length ≤ (encoding.encode c).length + 1 := by
  have hc : (encodingNatBool.encode c.value).length ≤ c.inputs + 1 := by
    change (encodeNat c.value).length ≤ _
    rw [Holant.Algebraic.encodeNat_length]
    exact le_trans (Nat.size_le_size (value_le c)) Nat.size_pow.le
  exact le_trans hc (Nat.add_le_add_right c.inputs_le_encoded_length 1)

noncomputable def outputBound : PolynomialOutputBound encoding encodingNatBool value where
  bound := Polynomial.X + 1
  length_le c := by simpa using output_length_le c

end Holant.LocalDrafts.CountingHardness.CircuitInstance
