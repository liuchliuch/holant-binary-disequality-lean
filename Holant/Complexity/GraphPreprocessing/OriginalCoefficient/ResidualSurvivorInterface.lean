import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

theorem input_length (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length =
      2*(RawClosedNetwork.encoding.encode x.1.val).length + 2*x.2.1.val +
      (RawClosedNetwork.endpointEncoding.encode (x.2.2.1.val,x.2.2.2)).length + 2 := by
  simp only [input_word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def timePolynomial (s : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  50*(Polynomial.X+1)^2 + Polynomial.C (2*maxArity s arity+20)

theorem ticks_le (x : Input s b arity) :
    ticks x ≤ (timePolynomial s arity).eval ((inputEncoding s b arity).encode x).length := by
  have hp := ResidualPin.ticks_le x.1.val x.1.property x.2.1 (x.1.val.lookup x.1.property x.2.2)
  have hin := input_length x
  have hr : (RawClosedNetwork.encoding.encode x.1.val).length ≤ ((inputEncoding s b arity).encode x).length := by omega
  have hs := Nat.mul_le_mul (Nat.add_le_add_right hr 1) (Nat.add_le_add_right hr 1)
  unfold ticks ResidualPin.timeBound timePolynomial at *
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one] at *
  nlinarith

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    BinaryCompose.Computes (inputEncoding s b arity) Frame.wordEncoding portBits where
  machine := machine
  time := timePolynomial s arity
  outputs x := {
    steps := ticks x
    evals_in_steps := exact_run x
    steps_le_m := ticks_le x }

theorem inFP : InFP (inputEncoding s b arity) Frame.wordEncoding portBits := (computes s b arity).inFP

/-- Original local-port meaning of the physical optional unary result. -/
def selected (x : Input s b arity) : Option (Fin (arity (x.1.val.vertices.get x.2.1).1)) :=
  (ResidualPin.selected true x.1.val x.2.1 (x.1.val.lookup x.1.property x.2.2)).map Prod.fst

theorem selected_encode (x : Input s b arity) :
    (optionEncoding (OccurrenceLabel.unaryPortEncoding (arity (x.1.val.vertices.get x.2.1).1))).encode
      (selected x) = portBits x := by
  unfold selected ResidualPin.selected portBits portWord
  split
  · rename_i h
    have hv := congrArg Fin.val h
    simp [optionEncoding,OccurrenceLabel.unaryPortEncoding,hv]
  · rename_i h
    have hv : (x.1.val.lookup x.1.property x.2.2).1.val ≠ x.2.1.val := fun e => h (Fin.ext e)
    simp [optionEncoding,hv]

theorem output_length (x : Input s b arity) : (portBits x).length ≤ maxArity s arity+1 := by
  let p := x.1.val.lookup x.1.property x.2.2
  have hi := p.2.isLt
  have ha := arity_le_maxArity arity (x.1.val.signatureLabel x.1.property p.1)
  change arity (x.1.val.vertices.get p.1).1 ≤ maxArity s arity at ha
  change (portWord p.1.val x.2.1.val p.2.val).length ≤ _
  unfold portWord
  split <;> simp only [List.length_cons,List.length_nil,List.length_replicate] <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorQuery
