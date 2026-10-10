import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoopInterface

/-! Actual raw closed-network bytes to the original unary endpoint table. The
vertex count and all edge-loop bounds come from executed framed-list counting;
no prepared graph, parent table or endpoint array is an input to this machine. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawEdgeTable
open Turing Computability BinaryCompose FixedFieldMachines
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

noncomputable def countsComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (EdgeTableLoop.packageEncoding s b arity) id :=
  recode CountsPackage.computes Subtype.val (fun _ => rfl) (fun _ => rfl)

abbrev machine : Machine := CountsPackage.machine.compose (EdgeTableLoop.machine EdgeWord.machine)

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding EdgeTableLoop.tableWord :=
  (countsComputes s b arity).andThen (EdgeTableLoop.computes (EdgeWord.computes s b arity))

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine = machine := rfl

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time

/-- The complete clean execution includes record counting, all provider calls,
all endpoint queries, all materialized unary IDs, framing and final cleanup. -/
noncomputable def timed (x : {r : RawClosedNetwork // r.WellFormed s b arity}) :
    TM2OutputsInTime machine.computer (RawClosedNetwork.encoding.encode x.val)
      (some (EdgeTableLoop.tableWord x))
      ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length) :=
  (computes s b arity).outputs x

theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding EdgeTableLoop.tableWord :=
  (computes s b arity).inFP

noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity * Polynomial.C machine.primitiveBudget

theorem primitive_bound (x : {r : RawClosedNetwork // r.WellFormed s b arity}) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (RawClosedNetwork.encoding.encode x.val))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (primitiveCost_le _ _ _) h

/-- Both original vertex metadata and every original edge-end word have their
size bounded directly by the raw graph's own encoded bit length. -/
theorem output_length (x : {r : RawClosedNetwork // r.WellFormed s b arity}) :
    (EdgeTableLoop.tableWord x).length ≤ 3*((RawClosedNetwork.encoding.encode x.val).length+1)^2 := by
  have hp := EdgeWord.prefix_length x.val x.property x.val.edges.length (le_refl _)
  rw [EdgeWord.prefix_full] at hp
  have hc := x.val.counts_le_encoded_length
  have hv : x.val.vertices.length≤(RawClosedNetwork.encoding.encode x.val).length := by omega
  have he : x.val.edges.length≤(RawClosedNetwork.encoding.encode x.val).length := by omega
  have hm := Nat.mul_le_mul hv he
  simp only [EdgeTableLoop.tableWord,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  nlinarith

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawEdgeTable
