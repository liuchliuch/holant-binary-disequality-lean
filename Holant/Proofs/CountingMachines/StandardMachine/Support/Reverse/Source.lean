import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Resources

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Sole general-machine interpreter entry.
This supplies the actual instruction/packet macro and full real-prefix costs,
not an assumed verifier Computes. It does NOT yet construct SharpPWitness:
the original typed tagged input -> readyCfg staging and the final acceptance/
EOF/all-stack cleanup machine and their timed proofs remain to be connected.
Nor is any separately chosen conventional #P model identified by definition.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Source
open Turing Holant.Complexity
variable (m : BinaryMachine)

def interpreter : FinTM2 := Program.computer m

/-- Universal physical round, for any delivered BinaryMachine, not merely a
machine produced from SharpPWitness. The only edge premise is the real original
edge being simulated. All interpreter correctness and costs have proof bodies.
-/
theorem arbitrary_round (token : Option Bool) (word : List Bool) (c d : m.Config)
    (h : m.step token c = some d) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m (Packet.encode token ++ word) c)) =
        some (Program.readyCfg m word d) ∧
    (Program.deterministic m).primitiveCost 3
      ([],Program.readyCfg m (Packet.encode token ++ word) c) ≤
        3 * (Program.deterministic m).primitiveBudget ∧
    ∀ (j : ℕ), j ≤ 3 → ∃ (next : (interpreter m).Cfg),
      (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[j]
        (some (Program.readyCfg m (Packet.encode token ++ word) c)) = some next ∧
      (Program.deterministic m).codedStorageBits next ≤
        (Program.deterministic m).controlBits +
        (2 + word.length + Program.sourceCells m c +
          3 * (Program.deterministic m).pushBudget) *
            (Program.deterministic m).symbolWidths := by
  have hr := Program.round m token word c d h
  refine ⟨hr,Program.round_primitive m token word c,?_⟩
  intro j hj
  obtain ⟨next,hp⟩ := Program.actual_prefix_exists m 3 j _ _ hr hj
  exact ⟨next,hp,Program.round_prefix_bits m token word c j hj next hp⟩

/-- The actual macro contract required by the existing TimedSimulation API is
produced here. The API's free simulate parameter is never a source argument.
-/
def roundExecution (token : Option Bool) (word : List Bool) (c d : m.Config)
    (h : m.step token c = some d) := Program.timed_round m token word c d h

theorem round_internal_bits (token : Option Bool) (word : List Bool) (c : m.Config)
    (j : ℕ) (hj : j < 3) (next : (interpreter m).Cfg) (l : (interpreter m).Λ)
    (h : (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[j]
      (some (Program.readyCfg m (Packet.encode token ++ word) c)) = some next) :
    Program.PrimitiveBitsBound m ((interpreter m).m l) next.var next.stk
      ((Program.deterministic m).controlBits +
        (2 + word.length + Program.sourceCells m c + 3 * (Program.deterministic m).pushBudget) *
          (Program.deterministic m).symbolWidths) :=
  Program.round_internal_bits m token word c j hj next l h

theorem malformed_packet (word : List Bool) (c : m.Config) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m (false :: true :: word) c)) =
      some (Program.rejectedCfg m (some false) (some true) word c) :=
  Program.invalid_round m false true word c rfl

theorem packet_eof (c : m.Config) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m [] c)) = some (Program.rejectedCfg m none none [] c) :=
  Program.empty_packet m c

theorem packet_odd (bit : Bool) (c : m.Config) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m [bit] c)) =
      some (Program.rejectedCfg m (some bit) none [] c) := Program.odd_packet m bit c

theorem forbidden_token (token : Option Bool) (word : List Bool) (c : m.Config)
    (h : m.step token c = none) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m (Packet.encode token ++ word) c)) =
      some (Program.rejectedCfg m (some (Packet.first token))
        (some (Packet.second token)) word c) :=
  Program.forbidden_round m token word c h

theorem ordinary_bool_rejected (l : m.core.Λ) (b : Bool) (word : List Bool)
    (c : m.Config) (hl : c.l = some l) (hs : m.split l = false) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m (Packet.encode (some b) ++ word) c)) =
      some (Program.rejectedCfg m (some true) (some b) word c) := by
  dsimp only [interpreter]
  simpa only [Packet.first,Packet.second] using
    Program.forbidden_round m (some b) word c (by simp [BinaryMachine.step,hl,hs])

theorem split_none_rejected (l : m.core.Λ) (word : List Bool)
    (c : m.Config) (hl : c.l = some l) (hs : m.split l = true) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m (false :: false :: word) c)) =
      some (Program.rejectedCfg m (some false) (some false) word c) :=
  Program.forbidden_round m none word c (by simp [BinaryMachine.step,hl,hs])

theorem halt_padding (word : List Bool) (c : m.Config) (hc : c.l = none) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m (false :: false :: word) c)) =
      some (Program.readyCfg m word c) :=
  Program.round m none word c c (m.step_halt c hc)

theorem halt_bool_rejected (b : Bool) (word : List Bool) (c : m.Config) (hc : c.l = none) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3]
      (some (Program.readyCfg m (Packet.encode (some b) ++ word) c)) =
      some (Program.rejectedCfg m (some true) (some b) word c) := by
  dsimp only [interpreter]
  simpa only [Packet.first,Packet.second] using
    Program.forbidden_round m (some b) word c (m.step_halt_no_choice c hc b)

/-- Simulate a whole genuine physical trace from the same literal original
input stack. This begins at the staged two-stack view, NOT at a fabricated
whole-verifier input initList; the missing staging obligation stays explicit.
-/
theorem arbitrary_trace (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (d : m.Config)
    (hlen : tokens.length = T.eval input.length)
    (htrace : m.TraceValid tokens (initList m.core input) d) :
    (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[3 * tokens.length]
      (some (Program.readyCfg m (tokens.flatMap Packet.encode) (initList m.core input))) =
        some (Program.readyCfg m [] d) ∧
    (Program.deterministic m).primitiveCost (3 * tokens.length)
      ([],Program.readyCfg m (tokens.flatMap Packet.encode) (initList m.core input)) ≤
        (Program.primitivePolynomial m T).eval input.length ∧
    ∀ (j : ℕ), j ≤ 3 * tokens.length → ∃ (next : (interpreter m).Cfg),
      (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[j]
        (some (Program.readyCfg m (tokens.flatMap Packet.encode) (initList m.core input))) = some next ∧
      (Program.deterministic m).codedStorageBits next ≤
        (Program.bitsPolynomial m T).eval input.length := by
  refine ⟨?_,Program.trace_primitive m T input tokens hlen,?_⟩
  · dsimp only [interpreter]
    simpa only [List.append_nil] using Program.trace_run m tokens [] _ d htrace
  · intro j hj
    have hr := Program.trace_run m tokens [] (initList m.core input) d htrace
    simp only [List.append_nil] at hr
    obtain ⟨next,hp⟩ := Program.actual_prefix_exists m (3*tokens.length) j _ _ hr hj
    exact ⟨next,hp,Program.trace_prefix_bits m T input tokens hlen j hj next hp⟩

theorem fixed_packet_length (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length) :
    (tokens.flatMap Packet.encode).length = (Polynomial.C 2 * T).eval input.length := by
  simp only [Program.packet_word_length,hlen,Polynomial.eval_mul,Polynomial.eval_C]

theorem trace_internal_bits (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length)
    (j : ℕ) (hj : j < 3 * tokens.length) (next : (interpreter m).Cfg) (l : (interpreter m).Λ)
    (h : (fun p : Option (interpreter m).Cfg => p.bind (interpreter m).step)^[j]
      (some (Program.readyCfg m (tokens.flatMap Packet.encode) (initList m.core input))) = some next) :
    Program.PrimitiveBitsBound m ((interpreter m).m l) next.var next.stk
      ((Program.bitsPolynomial m T).eval input.length) :=
  Program.trace_internal_bits m T input tokens hlen j hj next l h

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Source
