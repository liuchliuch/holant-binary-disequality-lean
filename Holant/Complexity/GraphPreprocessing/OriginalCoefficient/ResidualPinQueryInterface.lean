import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQueryFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option Elab.async false

def ticks (side : Bool) (x : Input s b arity) : ℕ :=
  ResidualPin.ticks x.1.val x.1.property x.2.1 (x.1.val.lookup x.1.property (x.2.2,side)) +
    3 * (RawClosedNetwork.encoding.encode x.1.val).length + 3 * x.2.1.val +
    2 * (encodeNat x.2.2.val).length + (RawClosedNetwork.endpointEncoding.encode (x.2.2.val,side)).length + 13

/-- Complete clean execution, including both input frames, endpoint construction,
original lookup, target comparison, source return and all final input cleanup. -/
theorem exact_run (side value : Bool) (x : Input s b arity) :
    RunsExactly (machine side value).computer.step
      (initList (machine side value).computer ((inputEncoding s b arity).encode x))
      (haltList (machine side value).computer (pinBits side value x)) (ticks side x) := by
  let raw := RawClosedNetwork.encoding.encode x.1.val
  let target := List.replicate x.2.1.val true
  let edge := encodeNat x.2.2.val
  let query := RawClosedNetwork.endpointEncoding.encode (x.2.2.val,side)
  have a := parse_raw side value raw (Holant.Algebraic.frame target ++ edge) []
  have b' := parse_target side value raw target edge []
  have c := make_query side value raw target edge []
  have d := call_pin side value x
  have e := cleanup side value raw query target (pinBits side value x)
  have f := halt_step side value (pinBits side value x)
  have all := ((((a.trans b').trans c).trans d).trans e).trans (runsExactly_one f)
  have ht : ticks side x = 1 + ((raw.length+query.length+target.length+3) +
      ((ResidualPin.ticks x.1.val x.1.property x.2.1 (x.1.val.lookup x.1.property (x.2.2,side))+1) +
        ((2 * edge.length+4) + (2 * (target.length+1) + 2 * (raw.length+1))))) := by
    simp only [ticks,raw,query,target,edge,List.length_replicate]
    omega
  rw [initial,input_word,ht]
  simpa only [machine,FinTM2.step,raw,target,edge,query] using all

theorem input_length (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length =
      2 * (RawClosedNetwork.encoding.encode x.1.val).length + 2 * x.2.1.val + (encodeNat x.2.2.val).length + 2 := by
  simp only [input_word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def timePolynomial (s : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  50 * (Polynomial.X+1)^2 + Polynomial.C (2 * maxArity s arity+20)

theorem ticks_le (side : Bool) (x : Input s b arity) :
    ticks side x ≤ (timePolynomial s arity).eval ((inputEncoding s b arity).encode x).length := by
  have hp := ResidualPin.ticks_le x.1.val x.1.property x.2.1 (x.1.val.lookup x.1.property (x.2.2,side))
  have hq := NetworkLookup.query_bits_le x.1.val x.1.property (x.1.val.lookup x.1.property (x.2.2,side))
  have he : x.1.val.portEndpoint x.1.property (x.1.val.lookup x.1.property (x.2.2,side)) = (x.2.2.val,side) :=
    congrArg (fun p : Fin x.1.val.edges.length × Bool => (p.1.val,p.2)) (x.1.val.route_lookup x.1.property (x.2.2,side))
  rw [he] at hq
  have hin := input_length x
  have hr : (RawClosedNetwork.encoding.encode x.1.val).length ≤ ((inputEncoding s b arity).encode x).length := by omega
  have hs := Nat.mul_le_mul (Nat.add_le_add_right hr 1) (Nat.add_le_add_right hr 1)
  unfold ticks ResidualPin.timeBound timePolynomial at *
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one] at *
  nlinarith

/-- An ordinary genuine Boolean-machine witness suitable for physical pairing. -/
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) (side value : Bool) :
    BinaryCompose.Computes (inputEncoding s b arity) Frame.wordEncoding (pinBits side value) where
  machine := machine side value
  time := timePolynomial s arity
  outputs x := {
    steps := ticks side x
    evals_in_steps := exact_run side value x
    steps_le_m := ticks_le side x }

/-- Word length follows from original fixed arities, independently of any runtime certificate. -/
theorem output_length (side value : Bool) (x : Input s b arity) :
    (pinBits side value x).length ≤ maxArity s arity + 2 := by
  let p := x.1.val.lookup x.1.property (x.2.2,side)
  have hi := p.2.isLt
  have ha := arity_le_maxArity arity (x.1.val.signatureLabel x.1.property p.1)
  change arity (x.1.val.vertices.get p.1).1 ≤ maxArity s arity at ha
  change (ResidualPin.pinWord value p.1.val x.2.1.val p.2.val).length ≤ _
  unfold ResidualPin.pinWord
  split <;> simp only [List.length_cons,List.length_nil,List.length_replicate] <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQuery
