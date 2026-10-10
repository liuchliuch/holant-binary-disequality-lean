import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Finish

namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def chunk (code : Code A) : List Bool := records (opEncoding e) code

abbrev driver : BinaryCompose.Machine :=
  machine (GraphCodeMachine.machine e C .closed)
    (chunk e [.zero]).reverse (chunk e [.one]).reverse
    (chunk e [.swap, .add]).reverse (chunk e [.swap, .mul]).reverse

def closedTime (root : A) (children : Forest A) : ℕ :=
  closedTicks e root children + ((codeEncoding e).encode (compileClosed root children)).length + 5

def bodyTicks : Descriptor A → ℕ
  | .dense => 3
  | .tree a ts => 2 * ((closedEncoding e).encode (a, ts)).length + closedTime e a ts +
      (chunk e (compileClosed a ts)).length + 7
  | .unicycle a ts b us =>
      2 * ((closedEncoding e).encode (a, ts)).length + 2 * ((closedEncoding e).encode (b, us)).length +
      closedTime e a ts + closedTime e b us +
      (chunk e (compileClosed a ts)).length + (chunk e (compileClosed b us)).length + 13

def descriptorTicks (d : Descriptor A) : ℕ := 2 * (encode e d).length + 3 + bodyTicks e d

/-- Uniform conversion retains the provider's exact recorded transition count. -/
private theorem executes_of_timed (m : BinaryCompose.Machine) (input output : List Bool) (t : ℕ)
    (h : TM2OutputsInTime m.computer input (some output) t) :
    Machine.Kernels.Executes m input output h.steps := h.evals_in_steps

variable (hlabels : ∀ x, (e.encode x).length ≤ C)
include hlabels

theorem closed_call (i : Fin 3) (input descriptor output count : List Bool) (root : A) (children : Forest A) :
    RunsExactly (driver e C).computer.step
      (active (GraphCodeMachine.machine e C .closed) (startPhase i) input
        (Holant.Algebraic.frame ((closedEncoding e).encode (root, children)) ++ descriptor) output count)
      (active (GraphCodeMachine.machine e C .closed) (afterPhase i) input descriptor
        ((chunk e (compileClosed root children)).reverse ++ output) count)
      (2 * ((closedEncoding e).encode (root, children)).length + closedTime e root children +
        (chunk e (compileClosed root children)).length + 5) := by
  apply call_exact
  have h := executes_of_timed _ _ _ _ ((closedComputes e C hlabels).outputs (root, children))
  change Machine.Kernels.Executes (GraphCodeMachine.machine e C .closed)
    ((closedEncoding e).encode (root, children))
    ((codeEncoding e).encode (compileClosed root children)) (closedTime e root children) at h
  simpa only [code_records, chunk] using h

/-- Every descriptor executes its actual zero, one or two closed-tree compilers.
The two residual chunks retain their order and receive the literal swap/add suffix. -/
theorem body_exact (d : Descriptor A) (input output count : List Bool) :
    RunsExactly (driver e C).computer.step
      (active (GraphCodeMachine.machine e C .closed) 3 input (encode e d) output count)
      (active (GraphCodeMachine.machine e C .closed) 0 input []
        ((chunk e (componentCode d)).reverse ++ output) (true :: count)) (bodyTicks e d) := by
  let m := GraphCodeMachine.machine e C .closed
  let z := (chunk e [.zero]).reverse
  let o := (chunk e [.one]).reverse
  let a := (chunk e [.swap, .add]).reverse
  let p := (chunk e [.swap, .mul]).reverse
  cases d with
  | dense =>
    have tag := tag_exact m z o a p false false input [] output count
    have load := push_exact m z o a p 17 20 z rfl input [] output count
    have done := finish_descriptor m z o a p input (z ++ output) count
    simpa [bodyTicks, encode, componentCode, driver, m, z, o, a, p] using
      ((runsExactly_one tag).trans (runsExactly_one load)).trans (runsExactly_one done)
  | tree root children =>
    let word := (closedEncoding e).encode (root, children)
    have tag := tag_exact m z o a p false true input (Holant.Algebraic.frame word) output count
    have call := closed_call e C hlabels 0 input [] output count root children
    have done := finish_descriptor m z o a p input ((chunk e (compileClosed root children)).reverse ++ output) count
    have all := ((runsExactly_one tag).trans (by simpa [word, startPhase, afterPhase, List.append_nil, driver, m, z, o, a, p] using call)).trans
      (runsExactly_one done)
    convert all using 1 <;> simp [bodyTicks, encode, componentCode, word, driver, m]; omega
  | unicycle root children other forest =>
    let left := (closedEncoding e).encode (root, children)
    let right := (closedEncoding e).encode (other, forest)
    let lc := chunk e (compileClosed root children)
    let rc := chunk e (compileClosed other forest)
    have tag := tag_exact m z o a p true false input
      (Holant.Algebraic.frame left ++ Holant.Algebraic.frame right) output count
    have first := closed_call e C hlabels 1 input (Holant.Algebraic.frame right) output count root children
    have second := closed_call e C hlabels 2 input [] (lc.reverse ++ output) count other forest
    have load := push_exact m z o a p 16 20 a rfl input [] (rc.reverse ++ (lc.reverse ++ output)) count
    have done := finish_descriptor m z o a p input (a ++ (rc.reverse ++ (lc.reverse ++ output))) count
    have all := ((((runsExactly_one tag).trans first).trans
      (by simpa [List.append_nil, startPhase, afterPhase, driver, m, z, o, a, p, left, right, lc, rc] using second)).trans (runsExactly_one load)).trans (runsExactly_one done)
    convert all using 1 <;>
      simp [bodyTicks, encode, componentCode, addCode, chunk, records_append, List.reverse_append,
        List.append_assoc, left, right, lc, rc, driver, m, a]; omega

/-- One full physical list entry, including its outer frame and both terminators. -/
theorem descriptor_exact (d : Descriptor A) (suffix output count : List Bool) :
    RunsExactly (driver e C).computer.step
      (active (GraphCodeMachine.machine e C .closed) 0
        (true :: Holant.Algebraic.frame (encode e d) ++ suffix) [] output count)
      (active (GraphCodeMachine.machine e C .closed) 0 suffix []
        ((chunk e (componentCode d)).reverse ++ output) (true :: count)) (descriptorTicks e d) := by
  have first := fetch_exact (GraphCodeMachine.machine e C .closed)
    (chunk e [.zero]).reverse (chunk e [.one]).reverse
    (chunk e [.swap, .add]).reverse (chunk e [.swap, .mul]).reverse (encode e d) suffix output count
  convert first.trans (body_exact e C hlabels d suffix output count) using 1
  simp [descriptorTicks, Nat.add_comm]

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
