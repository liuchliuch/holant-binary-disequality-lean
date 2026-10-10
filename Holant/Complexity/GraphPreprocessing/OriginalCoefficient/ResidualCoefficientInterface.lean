import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInput
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option Elab.async false

def ticks (x : Input s b arity) : ℕ :=
  ResidualVertex.ticks false x.1.1.val x.1.1.property x.1.2.1 x.2 +
    2 * ((ResidualPinQuery.inputEncoding s b arity).encode x.1).length +
    3 * (RawClosedNetwork.encoding.encode x.1.1.val).length + 3 * x.1.2.1.val +
    (encodeNat x.1.2.2.val).length + 3 * (ResidualVertex.descriptorWord x.1.1.val x.1.2.1 x.2).length + 14

/-- Entire clean execution through actual retained-input parsing and the real
original signature/residual-label provider, with every return and cleanup charged. -/
theorem exact_run (x : Input s b arity) :
    RunsExactly (machine s b arity).computer.step
      (initList (machine s b arity).computer ((inputEncoding s b arity).encode x))
      (haltList (machine s b arity).computer ((treeLabelEncoding s b arity).encode (literal s b arity x)))
      (ticks s b arity x) := by
  let context := (ResidualPinQuery.inputEncoding s b arity).encode x.1
  let raw := RawClosedNetwork.encoding.encode x.1.1.val
  let vertex := List.replicate x.1.2.1.val true
  let edge := encodeNat x.1.2.2.val
  let descriptor := ResidualVertex.descriptorWord x.1.1.val x.1.2.1 x.2
  let word := (treeLabelEncoding s b arity).encode (literal s b arity x)
  have a := parse_context s b arity context descriptor
  have c := parse_raw s b arity raw (Holant.Algebraic.frame vertex ++ edge) descriptor
  have d := parse_vertex s b arity raw vertex edge descriptor
  have e := clear_edge s b arity raw vertex edge descriptor
  have f := move_descriptor s b arity raw vertex descriptor
  have g := call_coefficient s b arity x
  have h := cleanup s b arity raw vertex descriptor word
  have last := halt_step s b arity word
  have all := ((((((a.trans c).trans d).trans e).trans f).trans g).trans h).trans (runsExactly_one last)
  have ht : ticks s b arity x = 1 + ((raw.length+vertex.length+descriptor.length+3) +
      ((ResidualVertex.ticks false x.1.1.val x.1.1.property x.1.2.1 x.2+1) +
        (2 * (descriptor.length+1) + ((edge.length+1) + (2 * (vertex.length+1) +
          (2 * (raw.length+1) + 2 * (context.length+1))))))) := by
    simp only [ticks,context,raw,vertex,edge,descriptor,List.length_replicate]
    omega
  rw [initial,ht]
  simpa only [machine,FinTM2.step,inputEncoding,sigmaEncoding,ResidualVertex.descriptorWord,context,raw,vertex,edge,descriptor,word] using all

theorem input_length (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length =
      2 * ((ResidualPinQuery.inputEncoding s b arity).encode x.1).length + 1 +
        (ResidualVertex.descriptorWord x.1.1.val x.1.2.1 x.2).length := by
  simp only [inputEncoding,sigmaEncoding,ResidualVertex.descriptorWord,List.length_append,Holant.Algebraic.frame_length]

noncomputable def timePolynomial : Polynomial ℕ :=
  30 * Polynomial.X + Polynomial.C (2 * ResidualLabel.inputBound s arity + 2 * s.size +
    2 * lengthBound s b arity + 40)

theorem ticks_le (x : Input s b arity) :
    ticks s b arity x ≤ (timePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length := by
  have h := ResidualVertex.ticks_le false x.1.1.val x.1.1.property x.1.2.1 x.2
  have hc := ResidualPinQuery.input_length x.1
  have hi := input_length s b arity x
  unfold ticks timePolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_C]
  omega

/-- The bridge is an ordinary finite Boolean-stack computation, with the unchanged label codec. -/
noncomputable def computes :
    BinaryCompose.Computes (inputEncoding s b arity) (treeLabelEncoding s b arity) (literal s b arity) where
  machine := machine s b arity
  time := timePolynomial s b arity
  outputs x := {
    steps := ticks s b arity x
    evals_in_steps := exact_run s b arity x
    steps_le_m := ticks_le s b arity x }

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInput
