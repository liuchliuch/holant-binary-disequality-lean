import Holant.Proofs.Algorithms.QuaternaryUnaryAccess
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.Tractability.ControlledComposition

/-! Repaired actual-query control for the original-L pure-pin source.
This separate leaf preserves the failed original source and its diagnostics.
The old accessOriginalL and its existentially chosen Poly reduction are untouched.
V2 selects actual dichotomy NETWORK data, then installs the existing literal
one- or three-query program with an actual-prefix byte certificate. The original
two power macros, factor chain, ports, tables and field conversions are reused.
Fixed-family noncomputable installation is explicit; no uniform recognition-time
claim or Poly-to-LengthControlled coercion is made.
-/
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentUnaryQueryControl
open Holant Holant.Tractable Holant.Algebraic Turing Computability
open Holant.Complexity BinaryCompose FixedFieldMachines OracleBatch StackProtocol
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open UniversalPairReduction FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain

namespace ThreeTrace
variable (a b : BinaryCompose.Machine)

/-- The old per-transition potential telescopes along the actual finite run.
Equal endpoint potentials therefore prove that a protocol segment makes no
query, rather than inferring this from its endpoint correctness. -/
private theorem potential_run (oracle : List Bool → List Bool)
    (start finish : (ThreeQuery.machine a b).Cfg) (n : ℕ)
    (hr : RunsExactly ((ThreeQuery.machine a b).step oracle) start finish n) :
    ThreeQuery.queryCount (ThreeQuery.machine a b) oracle start n+
      ThreeQuery.remaining a b finish ≤ ThreeQuery.remaining a b start := by
  induction n generalizing start with
  | zero =>
    have he : start=finish := Option.some.inj hr
    subst finish
    simpa only [ThreeQuery.queryCount,Nat.zero_add] using
      (Nat.le_refl (ThreeQuery.remaining a b start))
  | succ n ih =>
    change (fun p => p.bind ((ThreeQuery.machine a b).step oracle))^[n+1]
      (some start)=some finish at hr
    rw [Function.iterate_succ_apply] at hr
    cases hs : (ThreeQuery.machine a b).step oracle start with
    | none => simp [hs] at hr
    | some next =>
      have tail : RunsExactly ((ThreeQuery.machine a b).step oracle) next finish n := by
        change (fun p => p.bind ((ThreeQuery.machine a b).step oracle))^[n]
          (some next)=some finish
        simpa only [Option.bind_some,hs] using hr
      have ht := ih next tail
      have hp := ThreeQuery.potential a b oracle start next hs
      simp only [ThreeQuery.queryCount,hs]
      omega

private theorem silent (oracle : List Bool → List Bool)
    (start finish : (ThreeQuery.machine a b).Cfg) (n : ℕ)
    (hr : RunsExactly ((ThreeQuery.machine a b).step oracle) start finish n)
    (he : ThreeQuery.remaining a b finish=ThreeQuery.remaining a b start) :
    RunsTrace (ThreeQuery.machine a b) oracle start finish n [] := by
  refine ⟨hr,?_⟩
  apply List.eq_nil_of_length_eq_zero
  rw [queryTrace_length]
  have hp := potential_run a b oracle start finish n hr
  omega

private theorem call (oracle : List Bool → List Bool) (call next : Fin 21)
    (hp : ThreeQuery.protocol a b call=.query (fun _ => ThreeQuery.admin a b next))
    (suffix word one two : List Bool) :
    RunsTrace (ThreeQuery.machine a b) oracle
      (ThreeQuery.stageCfg a b call suffix word [] one two)
      (ThreeQuery.stageCfg a b next suffix (oracle word) [] one two) 1 [word] := by
  refine ⟨ThreeQuery.query_run a b oracle call next hp suffix word one two,?_⟩
  simp [queryTrace,queryWords,ThreeQuery.machine,OracleMachine.step,
    ThreeQuery.program,ThreeQuery.stageCfg,ThreeQuery.admin,hp,StackProtocol.cfg,
    ThreeQuery.tapes,StackProtocol.tapes3,ThreeQuery.queryKey,ThreeQuery.sourceKey,
    ThreeQuery.temporaryKey,ThreeQuery.savedOneKey,ThreeQuery.savedTwoKey,wordTape]

/-- Every framing/copy/save/emit segment is charged by its old exact-run
receipt. The resulting transcript contains the three original words in order. -/
theorem collector (oracle : List Bool → List Bool) (x y z context : List Bool) :
    ∃ n, RunsTrace (ThreeQuery.machine a b) oracle
      (ThreeQuery.leftCfg a b (haltList a.computer (ThreeQuery.word x y z context)))
      (ThreeQuery.stageCfg a b 18
        (ThreeQuery.word (oracle x) (oracle y) (oracle z) context) [] [] [] []) n [x,y,z] := by
  rw [ThreeQuery.left_halt]
  have e1 := silent a b oracle _ _ _
    (ThreeQuery.extract_run a b oracle 0 1 2 rfl rfl x
      (frame y ++ (frame z ++ context)) [] []) rfl
  have q1 := call a b oracle 2 3 rfl (frame y ++ (frame z ++ context)) x [] []
  have s1 := silent a b oracle _ _ _
    (ThreeQuery.save_one_run a b oracle (frame y ++ (frame z ++ context)) (oracle x) []) rfl
  have e2 := silent a b oracle _ _ _
    (ThreeQuery.extract_run a b oracle 4 5 6 rfl rfl y (frame z ++ context) (oracle x).reverse []) rfl
  have q2 := call a b oracle 6 7 rfl (frame z ++ context) y (oracle x).reverse []
  have s2 := silent a b oracle _ _ _
    (ThreeQuery.save_two_run a b oracle (frame z ++ context) (oracle y) (oracle x).reverse) rfl
  have e3 := silent a b oracle _ _ _
    (ThreeQuery.extract_run a b oracle 8 9 10 rfl rfl z context
      (oracle x).reverse (oracle y).reverse) rfl
  have q3 := call a b oracle 10 11 rfl context z (oracle x).reverse (oracle y).reverse
  have s3 := silent a b oracle _ _ _
    (ThreeQuery.emit_third_run a b oracle context (oracle z) (oracle x).reverse (oracle y).reverse) rfl
  have p2 := silent a b oracle _ _ _
    (ThreeQuery.emit_two_run a b oracle (frame (oracle z) ++ context) (oracle y) (oracle x).reverse) rfl
  have p1 := silent a b oracle _ _ _
    (ThreeQuery.emit_one_run a b oracle (frame (oracle y) ++ (frame (oracle z) ++ context)) (oracle x)) rfl
  have all := (((((((((e1.trans q1).trans s1).trans e2).trans q2).trans s2).trans e3).trans q3).trans s3).trans p2).trans p1
  simp only [List.nil_append,List.append_nil,List.cons_append] at all
  exact ⟨_,all⟩

/-- A completed pre/compiler/collector/post run has this exact transcript.
The finite machines are the old ThreeQuery.machine, with no host callback. -/
theorem whole (oracle : List Bool → List Bool) (input x y z context output : List Bool)
    (n m : ℕ)
    (ha : TM2OutputsInTime a.computer input (some (ThreeQuery.word x y z context)) n)
    (hb : TM2OutputsInTime b.computer
      (ThreeQuery.word (oracle x) (oracle y) (oracle z) context) (some output) m) :
    ∃ ticks, RunsTrace (ThreeQuery.machine a b) oracle
      ((ThreeQuery.machine a b).init input) ((ThreeQuery.machine a b).output output) ticks [x,y,z] := by
  have first := OracleOneQuery.ordinary_run (M:=ThreeQuery.machine a b)
    (ThreeQuery.leftLayout a b) (ThreeQuery.leftStates a b) (ThreeQuery.firstLabel a b)
    (some (ThreeQuery.admin a b 0)) (fun _ => rfl) oracle _ _ ha.steps ha.evals_in_steps
  change RunsExactly ((ThreeQuery.machine a b).step oracle)
    (ThreeQuery.leftCfg a b _) (ThreeQuery.leftCfg a b _) ha.steps at first
  rw [ThreeQuery.left_init] at first
  have firstTrace := silent a b oracle _ _ _ first (by
    simp [ThreeQuery.left_halt,ThreeQuery.remaining,ThreeQuery.remainingLabel,
      ThreeQuery.machine,OracleMachine.init,ThreeQuery.firstLabel,
      ThreeQuery.stageCfg,StackProtocol.cfg,ThreeQuery.admin])
  obtain ⟨collectorTicks,collect⟩ := collector a b oracle x y z context
  have transfer := silent a b oracle _ _ _
    (ThreeQuery.transfer_run a b oracle (ThreeQuery.word (oracle x) (oracle y) (oracle z) context)) (by
      rw [ThreeQuery.right_init]
      simp [ThreeQuery.remaining,ThreeQuery.remainingLabel,ThreeQuery.stageCfg,
        StackProtocol.cfg,ThreeQuery.admin,ThreeQuery.secondLabel])
  have last := OracleOneQuery.ordinary_run (M:=ThreeQuery.machine a b)
    (ThreeQuery.rightLayout a b) (ThreeQuery.rightStates a b) (ThreeQuery.secondLabel a b)
    none (fun _ => rfl) oracle _ _ hb.steps hb.evals_in_steps
  change RunsExactly ((ThreeQuery.machine a b).step oracle)
    (ThreeQuery.rightCfg a b _) (ThreeQuery.rightCfg a b _) hb.steps at last
  rw [ThreeQuery.right_halt] at last
  have lastTrace := silent a b oracle _ _ _ last (by
    rw [ThreeQuery.right_init]
    simp [ThreeQuery.remaining,ThreeQuery.remainingLabel,ThreeQuery.machine,
      OracleMachine.output,StackProtocol.cfg,ThreeQuery.secondLabel])
  have all := ((firstTrace.trans collect).trans transfer).trans lastTrace
  simp only [List.nil_append,List.append_nil] at all
  exact ⟨_,all⟩

variable {α β γ δ ε : Type}
variable {ea : Encoding α Bool} {eb : Encoding β Bool}
variable {eq : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
variable {pre : α → γ × (γ × (γ × ε))} {post : δ × (δ × (δ × ε)) → β} {g : γ → δ}

theorem query_origin (preProgram : Computes ea (ThreeQuery.contextEncoding eq ee) pre)
    (postProgram : Computes (ThreeQuery.contextEncoding ed ee) eb post)
    (size : PolynomialOutputBound eq ed g) (oracle : List Bool → List Bool)
    (ho : RepresentsOracle eq ed g oracle) (x : α) (t : ℕ)
    (c : (ThreeQuery.reduction preProgram postProgram size).machine.Cfg)
    (hr : (ThreeQuery.reduction preProgram postProgram size).machine.run oracle (ea.encode x) t=some c)
    (hq : (ThreeQuery.reduction preProgram postProgram size).machine.IsQuery c) :
    c.stk (ThreeQuery.reduction preProgram postProgram size).machine.queryStack=eq.encode (pre x).1 ∨
    c.stk (ThreeQuery.reduction preProgram postProgram size).machine.queryStack=eq.encode (pre x).2.1 ∨
    c.stk (ThreeQuery.reduction preProgram postProgram size).machine.queryStack=eq.encode (pre x).2.2.1 := by
  have hb : TM2OutputsInTime postProgram.machine.computer
        (ThreeQuery.word (oracle (eq.encode (pre x).1)) (oracle (eq.encode (pre x).2.1))
          (oracle (eq.encode (pre x).2.2.1)) (ee.encode (pre x).2.2.2))
        (some (eb.encode (post (ThreeQuery.answers g (pre x)))))
        (postProgram.time.eval ((ThreeQuery.contextEncoding ed ee).encode (ThreeQuery.answers g (pre x))).length) := by
      rw [ho (pre x).1,ho (pre x).2.1,ho (pre x).2.2.1]
      exact postProgram.outputs (ThreeQuery.answers g (pre x))
  obtain ⟨ticks,trace⟩ := whole preProgram.machine postProgram.machine oracle (ea.encode x)
      (eq.encode (pre x).1) (eq.encode (pre x).2.1) (eq.encode (pre x).2.2.1)
      (ee.encode (pre x).2.2.2) (eb.encode (post (ThreeQuery.answers g (pre x))))
      _ _ (preProgram.outputs x) hb
  have hm := TraceQueryControl.transcript_member trace t c hr hq
  simpa only [ThreeQuery.reduction,ThreeQuery.machine,
    List.mem_cons,List.not_mem_nil,or_false] using hm

/-- Upgrade only the literal three-query caller whose complete transcript was
proved above. The old time, answer charging and actual machine are retained. -/
def controlled (preProgram : Computes ea (ThreeQuery.contextEncoding eq ee) pre)
    (postProgram : Computes (ThreeQuery.contextEncoding ed ee) eb post)
    (size : PolynomialOutputBound eq ed g) :
    LengthControlledOracleReduction ea eb eq ed (fun x => post (ThreeQuery.answers g (pre x))) g where
  reduction := ThreeQuery.reduction preProgram postProgram size
  targetOutput := size
  queryBound := preProgram.outputBound.bound
  safeQuery oracle ho x t c hr hq := by
    have bounds := ThreeQuery.query_context_length_le preProgram x
    rcases query_origin preProgram postProgram size oracle ho x t c hr hq with h | h | h
    · exact ⟨(pre x).1,h,by rw [h]; exact bounds.1⟩
    · exact ⟨(pre x).2.1,h,by rw [h]; exact bounds.2.1⟩
    · exact ⟨(pre x).2.2.1,h,by rw [h]; exact bounds.2.2.1⟩

end ThreeTrace

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentUnaryQueryControl
