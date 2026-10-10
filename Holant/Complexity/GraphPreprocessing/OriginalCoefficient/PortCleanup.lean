import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortLookup

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortLookup
open Turing Computability StackProtocol BinaryCompose Holant.Algebraic
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- All copied query, edge, vertex and port streams are physically erased. -/
theorem cleanup_direct (source workerQuery portCount input vertices vertexCount raw query : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 4) source workerQuery portCount input vertices vertexCount raw query [])
      (config (.inr 8) [] [] portCount [] [] vertexCount raw query [])
      (source.length + workerQuery.length + input.length + vertices.length + 4) := by
  have a := clear_exact machine.computer.step (.inl (.inl 0) : Stack) (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) (true, none, ()) (tapes source workerQuery portCount input vertices vertexCount raw query [])
  have ha : Function.update (tapes source workerQuery portCount input vertices vertexCount raw query []) (.inl (.inl 0)) [] =
      tapes [] workerQuery portCount input vertices vertexCount raw query [] := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => rfl
    | inr k => rfl
  rw [ha] at a
  have b := clear_exact machine.computer.step (.inl (.inl 1) : Stack) (.inr 5) (.inr 6)
    (executesAt_tm2 _ _ _ rfl) (true, none, ()) (tapes [] workerQuery portCount input vertices vertexCount raw query [])
  have hb : Function.update (tapes [] workerQuery portCount input vertices vertexCount raw query []) (.inl (.inl 1)) [] =
      tapes [] [] portCount input vertices vertexCount raw query [] := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => rfl
    | inr k => rfl
  rw [hb] at b
  have c := clear_exact machine.computer.step (.inl (.inr 0) : Stack) (.inr 6) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) (true, none, ()) (tapes [] [] portCount input vertices vertexCount raw query [])
  have hc : Function.update (tapes [] [] portCount input vertices vertexCount raw query []) (.inl (.inr 0)) [] =
      tapes [] [] portCount [] vertices vertexCount raw query [] := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> rfl
    | inr k => rfl
  rw [hc] at c
  have d := clear_exact machine.computer.step (.inl (.inr 1) : Stack) (.inr 7) (.inr 8)
    (executesAt_tm2 _ _ _ rfl) (true, none, ()) (tapes [] [] portCount [] vertices vertexCount raw query [])
  have hd : Function.update (tapes [] [] portCount [] vertices vertexCount raw query []) (.inl (.inr 1)) [] =
      tapes [] [] portCount [] [] vertexCount raw query [] := by
    funext k; cases k with
    | inl k => cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> rfl
    | inr k => rfl
  rw [hd] at d
  simpa [config, cfg, WordEqual.cfg, WordEqual.clean, tapes, NetworkLookup.tapes, NetworkLookup.extras,
    FramedFind.tapes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ((a.trans b).trans c).trans d

variable {s b : ℕ} {arity : ℕ → ℕ}
def ticksExpanded (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) : ℕ :=
  2 * ((RawClosedNetwork.encoding.encode r).length + 1) +
  3 * (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)).length +
  NetworkLookup.portTime r h p +
  (framedListEncode RawClosedNetwork.endpointEncoding ((r.vertices.get p.1).2.drop (p.2.val + 1))).length +
  (framedListEncode encodingNatBool r.edges).length +
  (framedListEncode RawClosedNetwork.vertexEncoding (r.vertices.drop (p.1.val + 1))).length + 7

theorem ticksExpanded_eq_ticks (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    ticksExpanded r h p = ticks r h p := by
  unfold ticksExpanded ticks
  omega

/-- Original incidence inversion from real raw bytes, with both inputs preserved. -/
theorem exact_run (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] [] [] raw query [])
      (config (.inr 8) [] [] (List.replicate p.2.val true) [] [] (List.replicate p.1.val true) raw query [])
      (ticks r h p) := by
  have all := (((copy_raw _ _).trans (copy_query _ _)).trans (lookup r h p)).trans
    (cleanup _ _ _ _ _ _ _ _)
  convert all using 1
  unfold ticks
  omega

/-- The queried word is the original binary edge ID and orientation, not a port certificate. -/
theorem edge_exact (r : RawClosedNetwork) (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (q.1.val, q.2)
    let p := r.lookup h q
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] [] [] raw query [])
      (config (.inr 8) [] [] (List.replicate p.2.val true) [] [] (List.replicate p.1.val true) raw query [])
      (ticks r h p) := by
  have hp : r.portEndpoint h (r.lookup h q) = (q.1.val, q.2) :=
    congrArg (fun p : Fin r.edges.length × Bool => (p.1.val,p.2)) (r.route_lookup h q)
  simpa only [hp] using exact_run r h (r.lookup h q)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortLookup
