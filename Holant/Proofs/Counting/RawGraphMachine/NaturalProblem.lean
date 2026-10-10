import Holant.Proofs.Hardness.CircuitRawSemantics


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine.NaturalProblem

open Computability Holant Holant.Complexity
open scoped BigOperators

abbrev Input := {r : RawClosedNetwork // r.WellFormed 5 1 GateAlphabet.arity}
abbrev encoding := RawClosedNetwork.validatedEncoding 5 1 GateAlphabet.arity

def value (r : Input) : ℕ :=
  (r.val.realize r.property (GateAlphabet.signatures (K := ℕ))
    (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0

theorem value_eq_rows (r : Input) :
    value r = ∑ z : Fin r.val.edges.length → Bool,
      CircuitSemantics.rowsWeight r.val.vertices (NetworkSemantics.extend z) :=
  NetworkSemantics.denote_eq_rows r.val r.property

theorem row_weight_le_one (r : RawVertex) (ρ : ℕ → Bool) :
    (CircuitSemantics.rowWeight r ρ : ℕ) ≤ 1 := by
  unfold CircuitSemantics.rowWeight
  split
  all_goals simp only [GateAlphabet.pin, GateAlphabet.copy, GateAlphabet.nand]
  all_goals (try split_ifs) <;> omega

theorem rows_weight_le_one (rs : List RawVertex) (ρ : ℕ → Bool) :
    (CircuitSemantics.rowsWeight rs ρ : ℕ) ≤ 1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change CircuitSemantics.rowWeight r ρ * CircuitSemantics.rowsWeight rs ρ ≤ 1
    simpa using Nat.mul_le_mul (row_weight_le_one r ρ) ih

/-- A row-product really is an indicator, with no multiplicity or scalar
normalization hidden in the compressed equality-edge sum. -/
theorem rows_weight_indicator (rs : List RawVertex) (ρ : ℕ → Bool) :
    (CircuitSemantics.rowsWeight rs ρ : ℕ) =
      if (CircuitSemantics.rowsWeight rs ρ : ℕ) = 1 then 1 else 0 := by
  have h := rows_weight_le_one rs ρ
  split_ifs <;> omega

/-- This identifies the mathematical finite count. It does not assert a
polynomial-time graph verifier or a conventional #P machine equivalence. -/
theorem value_eq_countAccepted (r : Input) :
    value r = countAccepted (fun z : Fin r.val.edges.length → Bool =>
      decide ((CircuitSemantics.rowsWeight r.val.vertices (NetworkSemantics.extend z) : ℕ) = 1)) := by
  rw [value_eq_rows]
  unfold countAccepted
  apply Finset.sum_congr rfl
  intro z _
  simpa only [Bool.decide_iff] using
    rows_weight_indicator r.val.vertices (NetworkSemantics.extend z)

/-- Equality compression gives one independent Boolean choice per edge. All
five vertex weights are 0/1, including on loops and parallel-edge inputs. -/
theorem value_le (r : Input) : value r ≤ 2 ^ r.val.edges.length := by
  rw [value_eq_rows]
  calc
    (∑ z : Fin r.val.edges.length → Bool,
        CircuitSemantics.rowsWeight r.val.vertices (NetworkSemantics.extend z)) ≤
        ∑ _z : Fin r.val.edges.length → Bool, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro z _
      exact rows_weight_le_one _ _
    _ = 2 ^ r.val.edges.length := by simp

theorem output_length_le (r : Input) :
    (encodingNatBool.encode (value r)).length ≤ (encoding.encode r).length + 1 := by
  have hn : (encodingNatBool.encode (value r)).length ≤ r.val.edges.length + 1 := by
    change (encodeNat (value r)).length ≤ _
    rw [Holant.Algebraic.encodeNat_length]
    exact (Nat.size_le_size (value_le r)).trans Nat.size_pow.le
  have hg := r.val.counts_le_encoded_length
  change (encodingNatBool.encode (value r)).length ≤ (RawClosedNetwork.encoding.encode r.val).length + 1
  omega

def outputBound : PolynomialOutputBound encoding encodingNatBool value where
  bound := Polynomial.X + 1
  length_le r := by simpa using output_length_le r

theorem compiled_value (c : CircuitInstance) : value (RawCompiler.validated c) = c.value :=
  RawGraphMachine.value_nat c

end Holant.LocalDrafts.CountingHardness.RawGraphMachine.NaturalProblem
