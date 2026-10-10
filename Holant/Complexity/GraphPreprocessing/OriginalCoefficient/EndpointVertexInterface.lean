import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertexStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertex
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem cleanup (raw query vertex port : List Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 4) [] raw query vertex port [])
      (config (.inr 7) [] [] [] vertex [] []) (raw.length+query.length+port.length+3) := by
  have a := clear_exact (TM2.step program) rawKey (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] raw query vertex port [])
  rw [update_raw] at a
  change RunsExactly _ (config (.inr 4) [] raw query vertex port [])
    (config (.inr 5) [] [] query vertex port []) (raw.length+1) at a
  have b := clear_exact (TM2.step program) queryKey (.inr 5) (.inr 6)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] [] query vertex port [])
  rw [update_query] at b
  change RunsExactly _ (config (.inr 5) [] [] query vertex port [])
    (config (.inr 6) [] [] [] vertex port []) (query.length+1) at b
  have c := clear_exact (TM2.step program) portKey (.inr 6) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) (true,none,()) (work [] [] [] vertex port [])
  rw [update_port] at c
  change RunsExactly _ (config (.inr 6) [] [] [] vertex port [])
    (config (.inr 7) [] [] [] vertex [] []) (port.length+1) at c
  have ht : raw.length+query.length+port.length+3 = (port.length+1)+((query.length+1)+(raw.length+1)) := by omega
  rw [ht]
  exact (a.trans b).trans c

theorem work_empty : work [] [] [] [] [] [] = fun _ => [] := by decide

theorem initial (input : List Bool) :
    initList machine.computer input = config (.inr 0) input [] [] [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] [] [] [] [] input
  rw [work_empty] at h
  change wordTape inputKey input = _ at h
  unfold config WordEqual.cfg WordEqual.clean
  congr 1

theorem halt_step (vertex : List Bool) :
    TM2.step program (config (.inr 7) [] [] [] vertex [] []) = some (haltList machine.computer vertex) := by
  rw [Machine.halt_eq]
  have h := update_vertex [] [] [] [] [] [] vertex
  rw [work_empty] at h
  change wordTape outputKey vertex = _ at h
  change some (⟨none,WordEqual.clean true (),work [] [] [] vertex [] []⟩ : WordEqual.Config Stack Label Unit) = _
  rw [← h]

/-- A malformed frame or failed lookup has an explicit finite error flag.
In particular, it cannot be confused with clean vertex-zero output. -/
theorem error_step (state : WordEqual.Memory Unit) (tapes : Stack → List Bool) :
    machine.computer.step (⟨some (.inr 8),state,tapes⟩ : machine.Config) =
      some (⟨none,WordEqual.clean false (),tapes⟩ : machine.Config) := rfl

theorem error_distinct : WordEqual.clean false () ≠ machine.initial := by decide

variable {s b : ℕ} {arity : ℕ → ℕ}
def ticks (x : Input s b arity) : ℕ :=
  PortLookup.ticks x.1.val x.1.property (x.1.val.lookup x.1.property x.2) +
    3*(RawClosedNetwork.encoding.encode x.1.val).length+
    3*(RawClosedNetwork.endpointEncoding.encode (x.2.1.val,x.2.2)).length+
    (x.1.val.lookup x.1.property x.2).2.val+9

theorem exact_run (x : Input s b arity) :
    RunsExactly machine.computer.step (initList machine.computer ((inputEncoding s b arity).encode x))
      (haltList machine.computer (vertexBits x)) (ticks x) := by
  let raw := RawClosedNetwork.encoding.encode x.1.val
  let query := RawClosedNetwork.endpointEncoding.encode (x.2.1.val,x.2.2)
  let p := x.1.val.lookup x.1.property x.2
  have all := ((((parse_raw raw query).trans (move_query raw query)).trans (call_lookup x)).trans
    (cleanup raw query (vertexBits x) (List.replicate p.2.val true))).trans (runsExactly_one (halt_step (vertexBits x)))
  have ht : ticks x = 1+((raw.length+query.length+(List.replicate p.2.val true).length+3)+
      (PortLookup.ticks x.1.val x.1.property p+1+(2*(query.length+1)+2*(raw.length+1)))) := by
    simp only [ticks,raw,query,p,List.length_replicate]; omega
  rw [initial,input_word,ht]
  simpa only [machine,FinTM2.step,raw,query,p,vertexBits] using all

noncomputable def timePolynomial (s : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  40*(Polynomial.X+1)^2+Polynomial.C (maxArity s arity+10)

theorem ticks_le (x : Input s b arity) :
    ticks x ≤ (timePolynomial s arity).eval ((inputEncoding s b arity).encode x).length := by
  have hp := PortLookup.ticks_le x.1.val x.1.property (x.1.val.lookup x.1.property x.2)
  have ha := arity_le_maxArity arity (x.1.val.signatureLabel x.1.property (x.1.val.lookup x.1.property x.2).1)
  have hi := (x.1.val.lookup x.1.property x.2).2.isLt
  change arity (x.1.val.vertices.get (x.1.val.lookup x.1.property x.2).1).1 ≤ maxArity s arity at ha
  have hin : ((inputEncoding s b arity).encode x).length =
      2*(RawClosedNetwork.encoding.encode x.1.val).length+1+
        (RawClosedNetwork.endpointEncoding.encode (x.2.1.val,x.2.2)).length := by
    simp only [input_word,List.length_append,Holant.Algebraic.frame_length]
  have hr : (RawClosedNetwork.encoding.encode x.1.val).length ≤ ((inputEncoding s b arity).encode x).length := by omega
  have hs := Nat.mul_le_mul (Nat.add_le_add_right hr 1) (Nat.add_le_add_right hr 1)
  unfold ticks timePolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding vertexBits where
  machine := machine
  time := timePolynomial s arity
  outputs x := { steps := ticks x, evals_in_steps := exact_run x, steps_le_m := ticks_le x }

theorem inFP : InFP (inputEncoding s b arity) Frame.wordEncoding vertexBits := (computes s b arity).inFP

/-- The output is bounded by actual original vertex count, not a numeric input
identifier magnitude supplied by a caller. -/
theorem output_length (x : Input s b arity) :
    (vertexBits x).length < x.1.val.vertices.length := by
  simpa only [vertexBits,List.length_replicate] using (x.1.val.lookup x.1.property x.2).1.isLt

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointVertex
