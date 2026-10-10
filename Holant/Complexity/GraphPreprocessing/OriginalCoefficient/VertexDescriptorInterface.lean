import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexDescriptorFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexDescriptor
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option Elab.async false

def ticks (x : Input s b arity) : ℕ :=
  ResidualVertex.ticks false x.1.1.val x.1.1.property x.1.2 x.2 +
    2 * ((RawRootReach.inputEncoding s b arity).encode x.1).length +
    3 * (RawClosedNetwork.encoding.encode x.1.1.val).length + 3 * x.1.2.val +
    3 * (ResidualVertex.descriptorWord x.1.1.val x.1.2 x.2).length + 13

/-- Entire clean execution through actual retained-input parsing and the real
original signature/residual-label provider, with every return and cleanup charged. -/
theorem exact_run (x : Input s b arity) :
    RunsExactly (machine s b arity).computer.step
      (initList (machine s b arity).computer ((inputEncoding s b arity).encode x))
      (haltList (machine s b arity).computer ((treeLabelEncoding s b arity).encode (literal s b arity x)))
      (ticks s b arity x) := by
  let context := (RawRootReach.inputEncoding s b arity).encode x.1
  let raw := RawClosedNetwork.encoding.encode x.1.1.val
  let vertex := List.replicate x.1.2.val true
  let descriptor := ResidualVertex.descriptorWord x.1.1.val x.1.2 x.2
  let word := (treeLabelEncoding s b arity).encode (literal s b arity x)
  have a := parse_context s b arity context descriptor
  have c := parse_raw s b arity raw vertex descriptor
  have d := move_vertex s b arity raw vertex descriptor
  have f := move_descriptor s b arity raw vertex descriptor
  have g := call_coefficient s b arity x
  have h := cleanup s b arity raw vertex descriptor word
  have last := halt_step s b arity word
  have all := (((((a.trans c).trans d).trans f).trans g).trans h).trans (runsExactly_one last)
  have ht : ticks s b arity x = 1 + ((raw.length+vertex.length+descriptor.length+3) +
      ((ResidualVertex.ticks false x.1.1.val x.1.1.property x.1.2 x.2+1) +
        (2 * (descriptor.length+1) + (2 * (vertex.length+1) +
          (2 * (raw.length+1) + 2 * (context.length+1)))))) := by
    simp only [ticks,context,raw,vertex,descriptor,List.length_replicate]
    omega
  rw [initial,ht]
  simpa only [machine,FinTM2.step,inputEncoding,sigmaEncoding,ResidualVertex.descriptorWord,context,raw,vertex,descriptor,word] using all

theorem input_length (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length =
      2 * ((RawRootReach.inputEncoding s b arity).encode x.1).length + 1 +
        (ResidualVertex.descriptorWord x.1.1.val x.1.2 x.2).length := by
  simp only [inputEncoding,sigmaEncoding,ResidualVertex.descriptorWord,List.length_append,Holant.Algebraic.frame_length]

noncomputable def timePolynomial : Polynomial ℕ :=
  30 * Polynomial.X + Polynomial.C (2 * ResidualLabel.inputBound s arity + 2 * s.size +
    2 * lengthBound s b arity + 40)

theorem ticks_le (x : Input s b arity) :
    ticks s b arity x ≤ (timePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length := by
  have h := ResidualVertex.ticks_le false x.1.1.val x.1.1.property x.1.2 x.2
  have hc : ((RawRootReach.inputEncoding s b arity).encode x.1).length =
      2*(RawClosedNetwork.encoding.encode x.1.1.val).length+1+x.1.2.val := by
    change (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.1.val)++List.replicate x.1.2.val true).length=_
    simp [Holant.Algebraic.frame_length]
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

theorem inFP : InFP (inputEncoding s b arity) (treeLabelEncoding s b arity) (literal s b arity) :=
  (computes s b arity).inFP

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget

theorem primitive_bound (x : Input s b arity) :
    FixedFieldMachines.primitiveCost (machine s b arity) (ticks s b arity x)
      (some (initList (machine s b arity).computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (ticks_le s b arity x)
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (FixedFieldMachines.primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexDescriptor
