import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinStages
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinSpec
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option Elab.async false

def localTicks (vertex target port : ℕ) : ℕ :=
  (if vertex=target then 2 * (port+1) + 1 else port+2) + ((max vertex target+1) + 2 * (target+1))

theorem finish_exact (value : Bool) (raw query : List Bool) (vertex target port : ℕ) (output : List Bool) :
    RunsExactly (machine value).computer.step
      (config (.inr 0) true raw query (List.replicate vertex true) (List.replicate port true)
        (List.replicate target true) [] [] output)
      (config (.inr 8) true raw query [] [] (List.replicate target true) [] []
        (pinWord value vertex target port ++ output)) (localTicks vertex target port) := by
  have copy := copy_target value raw query (List.replicate vertex true) (List.replicate port true)
    (List.replicate target true) output
  have cmp := compare_vertex value vertex target raw query (List.replicate port true) output
  by_cases same : vertex=target
  · have cmp' : RunsExactly (machine value).computer.step
        (config (.inr 2) true raw query (List.replicate vertex true) (List.replicate port true)
          (List.replicate target true) (List.replicate target true) [] output)
        (config (.inr 3) true raw query [] (List.replicate port true) (List.replicate target true) [] [] output)
        (max vertex target+1) := by simpa only [machine,FinTM2.step,same,↓reduceIte,decide_true] using cmp
    have move := move_port value raw query (List.replicate port true) (List.replicate target true) output
    have tag := some_tag value raw query (List.replicate target true) (List.replicate port true ++ output)
    have all := ((copy.trans cmp').trans move).trans (runsExactly_one tag)
    have ht : localTicks vertex target port = 1 + (2 * ((List.replicate port true).length+1) +
        ((max vertex target+1) + 2 * ((List.replicate target true).length+1))) := by
      simp only [localTicks,same,↓reduceIte,List.length_replicate]
      omega
    rw [ht]
    simpa only [machine,FinTM2.step,pinWord,same,↓reduceIte,List.cons_append] using all
  · have cmp' : RunsExactly (machine value).computer.step
        (config (.inr 2) true raw query (List.replicate vertex true) (List.replicate port true)
          (List.replicate target true) (List.replicate target true) [] output)
        (config (.inr 6) false raw query [] (List.replicate port true) (List.replicate target true) [] [] output)
        (max vertex target+1) := by simpa only [machine,FinTM2.step,same,↓reduceIte,decide_false] using cmp
    have clear := clear_port value raw query (List.replicate port true) (List.replicate target true) output
    have tag := none_tag value raw query (List.replicate target true) output
    have all := ((copy.trans cmp').trans clear).trans (runsExactly_one tag)
    have ht : localTicks vertex target port = 1 + (((List.replicate port true).length+1) +
        ((max vertex target+1) + 2 * ((List.replicate target true).length+1))) := by
      simp only [localTicks,same,↓reduceIte,List.length_replicate]
      omega
    rw [ht]
    simpa only [machine,FinTM2.step,pinWord,same,↓reduceIte,List.cons_append,List.nil_append] using all

def ticks (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length) (p : r.Ports arity) : ℕ :=
  localTicks p.1.val v.val p.2.val + (PortLookup.ticks r h p + 1)

/-- Every emitted pin comes from a physical search and comparison at the original vertex. -/
theorem exact_run (value : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (p : r.Ports arity) (output : List Bool) :
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)
    RunsExactly (machine value).computer.step
      (config (.inl (.inr 0)) true raw query [] [] (List.replicate v.val true) [] [] output)
      (config (.inr 8) true raw query [] [] (List.replicate v.val true) [] []
        ((optionEncoding (ResidualLabel.pinEncoding (arity (r.vertices.get v).1))).encode (selected value r v p) ++ output))
      (ticks r h v p) := by
  rw [selected_encode]
  exact (lookup value r h p (List.replicate v.val true) output).trans
    (finish_exact value _ _ p.1.val v.val p.2.val output)

/-- The actual input is an original edge/end query, never a precomputed local pin. -/
theorem edge_exact (value : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (q : Fin r.edges.length × Bool) (output : List Bool) :
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (q.1.val,q.2)
    RunsExactly (machine value).computer.step
      (config (.inl (.inr 0)) true raw query [] [] (List.replicate v.val true) [] [] output)
      (config (.inr 8) true raw query [] [] (List.replicate v.val true) [] []
        ((optionEncoding (ResidualLabel.pinEncoding (arity (r.vertices.get v).1))).encode
          (selected value r v (r.lookup h q)) ++ output)) (ticks r h v (r.lookup h q)) := by
  have hp : r.portEndpoint h (r.lookup h q) = (q.1.val,q.2) :=
    congrArg (fun p : Fin r.edges.length × Bool => (p.1.val,p.2)) (r.route_lookup h q)
  simpa only [hp] using exact_run value r h v (r.lookup h q) output

def timeBound (s : ℕ) (arity : ℕ → ℕ) (L : ℕ) : ℕ := 32 * (L+1)^2 + 2 * maxArity s arity + 7

theorem ticks_le (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (p : r.Ports arity) :
    ticks r h v p ≤ timeBound s arity (RawClosedNetwork.encoding.encode r).length := by
  have hl := PortLookup.ticks_le r h p
  have hn := framedListEncode_length_lower RawClosedNetwork.vertexEncoding r.vertices
  have hv := v.isLt
  have hpv := p.1.isLt
  have hpp := p.2.isLt
  have ha := arity_le_maxArity arity (r.signatureLabel h p.1)
  change arity (r.vertices.get p.1).1 ≤ maxArity s arity at ha
  have hr : (RawClosedNetwork.encoding.encode r).length =
      2 * (framedListEncode RawClosedNetwork.vertexEncoding r.vertices).length + 1 +
        (framedListEncode encodingNatBool r.edges).length :=
    framedProductEncoding_length (framedListEncoding RawClosedNetwork.vertexEncoding) (framedListEncoding encodingNatBool) _
  have hm : max p.1.val v.val ≤ (RawClosedNetwork.encoding.encode r).length := by omega
  unfold ticks localTicks timeBound
  split <;> nlinarith

theorem primitive_bound (value : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (p : r.Ports arity) (output : List Bool) :
    FixedFieldMachines.primitiveCost (machine value) (ticks r h v p)
      (some (config (.inl (.inr 0)) true (RawClosedNetwork.encoding.encode r)
        (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)) [] [] (List.replicate v.val true) [] [] output)) ≤
      timeBound s arity (RawClosedNetwork.encoding.encode r).length * (machine value).primitiveBudget :=
  le_trans (FixedFieldMachines.primitiveCost_le _ _ _) (Nat.mul_le_mul_right _ (ticks_le r h v p))

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
