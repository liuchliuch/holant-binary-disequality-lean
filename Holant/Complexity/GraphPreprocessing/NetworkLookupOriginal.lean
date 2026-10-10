import Holant.Complexity.GraphPreprocessing.NetworkLookupBounds

/-! The nested finite machine implements original endpoint inverse lookup on
actual raw-network bits. No inverse-incidence table or decomposition certificate
is supplied to the running machine. Validation is used only to prove its target
exists uniquely. Costs include the entire executed parsing/search/copy pipeline. -/
namespace Holant.Complexity.GraphPreprocessing.NetworkLookup
open Turing Computability StackProtocol RawClosedNetwork
variable {s b : ℕ} {arity : ℕ → ℕ}

/-- Validated original incidence excludes the target from every earlier vertex. -/
theorem earlier_vertices_exclude (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    ∀ row ∈ r.vertices.take p.1.val, ∀ a ∈ row.2, a ≠ r.portEndpoint h p := by
  intro row hrow a ha he
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hrow
  have hj' : j < p.1.val := by simp only [List.length_take] at hj; omega
  let v : Fin r.vertices.length := ⟨j, Nat.lt_trans hj' p.1.isLt⟩
  have hv : r.vertices.get v = row := by simpa [v, List.get_eq_getElem] using hjv
  rw [← hv] at ha
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp ha
  let q : r.Ports arity := ⟨v, Fin.cast (h.1 v).2 k⟩
  have hq : r.portEndpoint h q = a := by simpa [portEndpoint, q] using hk
  have hp : r.portEndpoint h q = r.portEndpoint h p := hq.trans he
  have hr : r.route h q = r.route h p := by
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hp
    · change (r.portEndpoint h q).2 = (r.portEndpoint h p).2
      exact congrArg Prod.snd hp
  have eqp := (r.route_bijective h).1 hr
  have eqv := congrArg (fun p : r.Ports arity => p.1.val) eqp
  change j = p.1.val at eqv
  omega

def portTime (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) : ℕ :=
  2 * ((framedListEncode vertexEncoding r.vertices).length + 1) +
  scanTicks (r.vertices.take p.1.val) (r.vertices.get p.1) (Fin.cast (h.1 p.1).2.symm p.2)

def portInput (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) : machine.Config :=
  config (.inr 0) [] (endpointEncoding.encode (r.portEndpoint h p)) [] (encoding.encode r) [] [] []

def portResult (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) : machine.Config :=
  config (.inr 8) (framedListEncode endpointEncoding ((r.vertices.get p.1).2.drop (p.2.val + 1)))
    (endpointEncoding.encode (r.portEndpoint h p)) (List.replicate p.2.val true)
    (framedListEncode encodingNatBool r.edges)
    (framedListEncode vertexEncoding (r.vertices.drop (p.1.val + 1))) [] (List.replicate p.1.val true)

/-- The exact executed machine recovers both original incidence coordinates. -/
theorem original_port_exact (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    RunsExactly machine.computer.step (portInput r h p) (portResult r h p) (portTime r h p) := by
  have hx : r.vertices.take p.1.val ++ r.vertices.get p.1 :: r.vertices.drop (p.1.val + 1) = r.vertices := by
    rw [List.get_eq_getElem, List.getElem_cons_drop p.1.isLt, List.take_append_drop]
  have hn : (r.vertices.take p.1.val).length = p.1.val := by simp
  have first := outer_exact (framedListEncode vertexEncoding r.vertices) (framedListEncode encodingNatBool r.edges)
    (endpointEncoding.encode (r.portEndpoint h p))
  have second := scan_vertices (r.vertices.take p.1.val) (r.vertices.drop (p.1.val + 1))
    (r.vertices.get p.1) (Fin.cast (h.1 p.1).2.symm p.2) (PortSearch.vertex_ports_nodup r h p.1)
    (earlier_vertices_exclude r h p) [] (framedListEncode encodingNatBool r.edges) []
  simp only [hx, hn, List.append_nil] at second
  have run := first.trans second
  convert run using 1
  · rfl
  · rfl
  · unfold portTime
    omega

/-- Every relevant label/ID payload is bounded by the true whole-input bit length. -/
theorem query_bits_le (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    (endpointEncoding.encode (r.portEndpoint h p)).length ≤ (encoding.encode r).length := by
  have hport := element_bits_le endpointEncoding (r.vertices.get p.1).2 (r.portEndpoint h p)
    (List.get_mem _ (Fin.cast (h.1 p.1).2.symm p.2))
  have hvertex := element_bits_le vertexEncoding r.vertices (r.vertices.get p.1) (List.get_mem _ p.1)
  have hr : (vertexEncoding.encode (r.vertices.get p.1)).length =
      2 * (encodeNat (r.vertices.get p.1).1).length + 1 +
      (framedListEncode endpointEncoding (r.vertices.get p.1).2).length :=
    framedProductEncoding_length encodingNatBool (framedListEncoding endpointEncoding) _
  have hn : (encoding.encode r).length = 2 * (framedListEncode vertexEncoding r.vertices).length + 1 +
      (framedListEncode encodingNatBool r.edges).length :=
    framedProductEncoding_length (framedListEncoding vertexEncoding) (framedListEncoding encodingNatBool) _
  omega

/-- Full original-incidence lookup has a quadratic physical-input transition bound. -/
theorem portTime_le (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    portTime r h p ≤ 18 * ((encoding.encode r).length + 1)^2 := by
  have hx : r.vertices.take p.1.val ++ r.vertices.get p.1 :: r.vertices.drop (p.1.val + 1) = r.vertices := by
    rw [List.get_eq_getElem, List.getElem_cons_drop p.1.isLt, List.take_append_drop]
  have hs := scanTicks_le (r.vertices.take p.1.val) (r.vertices.drop (p.1.val + 1))
    (r.vertices.get p.1) (Fin.cast (h.1 p.1).2.symm p.2)
  rw [hx] at hs
  have hq := query_bits_le r h p
  have hn : (encoding.encode r).length = 2 * (framedListEncode vertexEncoding r.vertices).length + 1 +
      (framedListEncode encodingNatBool r.edges).length :=
    framedProductEncoding_length (framedListEncoding vertexEncoding) (framedListEncoding encodingNatBool) _
  change _ ≤ 16 * ((framedListEncode vertexEncoding r.vertices).length + 1) *
    ((endpointEncoding.encode (r.portEndpoint h p)).length + 1) at hs
  unfold portTime
  nlinarith

def original_port_correct (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    StateTransition.EvalsToInTime machine.computer.step (portInput r h p) (some (portResult r h p))
      (18 * ((encoding.encode r).length + 1)^2) where
  steps := portTime r h p
  evals_in_steps := original_port_exact r h p
  steps_le_m := portTime_le r h p

/-- Independent primitive execution counts every Boolean operation, including
all nested query copies, frame tests, and prior-vertex counter cleanup. -/
theorem original_port_bit_cost (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    (Primitive.run machine.program (portTime r h p) (some (portInput r h p))).2 = some (portResult r h p) ∧
    (Primitive.run machine.program (portTime r h p) (some (portInput r h p))).1 ≤
      144 * ((encoding.encode r).length + 1)^2 := by
  have hr := Primitive.execution_cost machine.program 8 program_budget (portTime r h p)
    (portInput r h p) (portResult r h p) (original_port_exact r h p)
  refine ⟨hr.1, le_trans hr.2 ?_⟩
  have ht := portTime_le r h p
  omega

/-- Substitute the proven executable original inverse, with the original queried
edge ID/orientation on the actual query stack, not an incidence certificate. -/
theorem lookup_exact (r : RawClosedNetwork) (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    RunsExactly machine.computer.step
      (config (.inr 0) [] (endpointEncoding.encode (q.1.val, q.2)) [] (encoding.encode r) [] [] [])
      (portResult r h (r.lookup h q)) (portTime r h (r.lookup h q)) := by
  have hp : r.portEndpoint h (r.lookup h q) = (q.1.val, q.2) :=
    congrArg (fun p : Fin r.edges.length × Bool => (p.1.val, p.2)) (r.route_lookup h q)
  have run := original_port_exact r h (r.lookup h q)
  simpa only [portInput, hp] using run

@[simp] theorem result_vertex (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    ((portResult r h p).stk (.inr 3)).length = p.1.val := by simp [portResult, config, WordEqual.cfg, tapes, extras]
@[simp] theorem result_port (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    ((portResult r h p).stk (.inl 6)).length = p.2.val := by simp [portResult, config, WordEqual.cfg, tapes, FramedFind.tapes]

end Holant.Complexity.GraphPreprocessing.NetworkLookup
