import Holant.Complexity.OracleBatch.ReductionTrace
import Holant.Complexity.OracleReductionCompose


namespace Holant.LocalDrafts.MainChain.TraceQueryControl
open Computability Holant.Complexity Holant.Complexity.OracleBatch
open Holant.Complexity.BinaryCompose

theorem iterate_none (m : OracleMachine) (oracle : List Bool → List Bool) (n : ℕ) :
    (fun c : Option m.Cfg => c.bind (m.step oracle))^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply']; simp only [ih, Option.bind_none]

/-- Determinism and the actual terminal configuration suffice: no label-level
syntactic count, execution prefix bound, or query-validity assumption is used. -/
theorem query_mem_trace (m : OracleMachine) (oracle : List Bool → List Bool)
    (output : List Bool) (n : ℕ) (start : m.Cfg)
    (hhalt : (fun c : Option m.Cfg => c.bind (m.step oracle))^[n]
      (some start) = some (m.output output))
    (t : ℕ) (c : m.Cfg)
    (hr : (fun c : Option m.Cfg => c.bind (m.step oracle))^[t]
      (some start) = some c) (hq : m.IsQuery c) :
    c.stk m.queryStack ∈ queryTrace m oracle start n := by
  induction n generalizing start t c with
  | zero =>
    have he : start = m.output output := Option.some.inj hhalt
    subst start
    cases t with
    | zero =>
      have he : m.output output = c := Option.some.inj hr
      subst c
      rcases hq with ⟨l,next,hl,_⟩
      simp [OracleMachine.output] at hl
    | succ t =>
      simp only [Function.iterate_succ_apply, Option.bind_some,
        OracleMachine.step_output, iterate_none] at hr
      contradiction
  | succ n ih =>
    cases hs : m.step oracle start with
    | none =>
      simp only [Function.iterate_succ_apply, Option.bind_some, hs, iterate_none] at hhalt
      contradiction
    | some next =>
      have htail : (fun c : Option m.Cfg => c.bind (m.step oracle))^[n]
          (some next) = some (m.output output) := by
        simpa only [Function.iterate_succ_apply, Option.bind_some, hs] using hhalt
      cases t with
      | zero =>
        have he : start = c := Option.some.inj hr
        subst c
        rcases hq with ⟨l,k,hl,hp⟩
        simp [queryTrace, hs, queryWords, hl, hp]
      | succ t =>
        have hr' : (fun c : Option m.Cfg => c.bind (m.step oracle))^[t]
            (some next) = some c := by
          simpa only [Function.iterate_succ_apply, Option.bind_some, hs] using hr
        have hm := ih next htail t c hr' hq
        simp only [queryTrace, hs, List.mem_append]
        exact Or.inr hm

theorem transcript_member {m : OracleMachine} {oracle : List Bool → List Bool}
    {input output : List Bool} {n : ℕ} {qs : List (List Bool)}
    (h : RunsTrace m oracle (m.init input) (m.output output) n qs)
    (t : ℕ) (c : m.Cfg) (hr : m.run oracle input t = some c) (hq : m.IsQuery c) :
    c.stk m.queryStack ∈ qs := by
  rw [← h.trace]
  exact query_mem_trace m oracle output n (m.init input) h.run t c hr hq

variable {α β γ δ ε : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {eq : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
    {pre : α → List γ × ε} {post : List δ × ε → β} {g : γ → δ}

/-- Actual batch preprocessing and postprocessing supply their own transcript;
the bound follows from the fully framed list produced by the preprocessor. -/
noncomputable def controlledBatch (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g) :
    LengthControlledOracleReduction ea eb eq ed (fun x => post (answers g (pre x))) g where
  reduction := OracleBatch.reduction a b size
  targetOutput := size
  queryBound := a.outputBound.bound
  safeQuery oracle ho x t c hr hq := by
    obtain ⟨n,_,htrace⟩ := reduction_run_trace a b size oracle ho x
    have hm := transcript_member htrace t c hr hq
    obtain ⟨q,hqmem,he⟩ := List.mem_map.mp hm
    refine ⟨q,he.symm,?_⟩
    exact (member_length_le _ _ hm).trans (query_context_length_le a x).1

end Holant.LocalDrafts.MainChain.TraceQueryControl
