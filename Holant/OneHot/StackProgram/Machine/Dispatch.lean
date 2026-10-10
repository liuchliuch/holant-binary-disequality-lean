import Holant.OneHot.StackProgram.Serialization
import Holant.Complexity.GraphPreprocessing.FrameMachine

/-!
# Actual finite opcode fetch and dispatch

A finite unrolled Boolean decision tree decodes a bounded opcode word. No list,
natural counter, field element, or decoding function is stored in machine state.
The decoder is evaluated only on the fixed words labelling syntax branches.
Fetch removes the list-entry marker, executes the proved bitwise unframer, and
dispatches after consuming the opcode word. All caller memory and other tapes
are preserved. This is an operational interpreter stage, not a full interpreter.
-/
namespace Holant.OneHot.StackProgram.Machine.Dispatch
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt
variable {A K Λ τ : Type} [DecidableEq K]

/-- A bounded, statically unrolled decoder. EOF invokes the compile-time leaf;
extra bits after the bound go to `bad`. Its only register is `Option Bool`. -/
def decodeStmt (src : K) (leaf : List Bool → Λ) (bad : Λ) :
    ℕ → List Bool → Stmt K Λ τ
  | 0, pre =>
      pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
        (load (fun v => (none, v.2)) (goto (fun _ => bad)))
        (load (fun v => (none, v.2)) (goto (fun _ => leaf pre))))
  | fuel + 1, pre =>
      pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
        (branch (fun v => v.1.getD false)
          (decodeStmt src leaf bad fuel (pre ++ [true]))
          (decodeStmt src leaf bad fuel (pre ++ [false])))
        (load (fun v => (none, v.2)) (goto (fun _ => leaf pre))))

/-- The decision tree acts entirely through actual pop/branch/load/goto syntax. -/
theorem decodeStmt_exact (src : K) (leaf : List Bool → Λ) (bad : Λ)
    (fuel : ℕ) (pre word : List Bool) (h : word.length ≤ fuel)
    (v : Option Bool × τ) (tapes : K → List Bool) :
    TM2.stepAux (decodeStmt src leaf bad fuel pre) v
        (Function.update tapes src word) =
      cfg (leaf (pre ++ word)) v.2 (Function.update tapes src []) := by
  induction fuel generalizing pre word v with
  | zero =>
    have hw : word = [] := List.length_eq_zero_iff.mp (by omega)
    subst word
    simp [decodeStmt, TM2.stepAux, cfg]
  | succ fuel ih =>
    cases word with
    | nil => simp [decodeStmt, TM2.stepAux, cfg]
    | cons bit word =>
      have hw : word.length ≤ fuel := by simp only [List.length_cons] at h; omega
      cases bit with
      | false =>
        simpa [decodeStmt, TM2.stepAux, List.append_assoc, Function.update_idem] using
          ih (pre ++ [false]) word hw (some false, v.2)
      | true =>
        simpa [decodeStmt, TM2.stepAux, List.append_assoc, Function.update_idem] using
          ih (pre ++ [true]) word hw (some true, v.2)

omit [DecidableEq K] in
/-- Even the nested decision tree has a linear per-transition primitive budget. -/
theorem decodeStmt_budget (src : K) (leaf : List Bool → Λ) (bad : Λ)
    (fuel : ℕ) (pre : List Bool) :
    TM2Cost.budget (decodeStmt (τ := τ) src leaf bad fuel pre) ≤ 3 * fuel + 4 := by
  induction fuel generalizing pre with
  | zero => rfl
  | succ fuel ih =>
    simp only [decodeStmt, TM2Cost.budget]
    have ht := ih (pre ++ [true])
    have hf := ih (pre ++ [false])
    omega

/-- Decode an opcode from exactly its serialized word. -/
def opcodeStmt (src : K) (labels : Op A → Λ) (bad : Λ)
    (e : Encoding A Bool) (fuel : ℕ) : Stmt K Λ τ :=
  decodeStmt src (fun bits => (opDecode e bits).elim bad labels) bad fuel []

theorem opcodeStmt_exact (src : K) (labels : Op A → Λ) (bad : Λ)
    (e : Encoding A Bool) (fuel : ℕ) (op : Op A)
    (h : (opEncode e op).length ≤ fuel) (memory : τ) (tapes : K → List Bool) :
    TM2.stepAux (opcodeStmt src labels bad e fuel) (none, memory)
      (Function.update tapes src (opEncode e op)) =
      cfg (labels op) memory (Function.update tapes src []) := by
  simpa [opcodeStmt] using decodeStmt_exact src
    (fun bits => (opDecode e bits).elim bad labels) bad fuel [] (opEncode e op) h
    (none, memory) tapes

/-- EOF before the list terminator, and trailing bits after it, reject. -/
def fetchStmt (src : K) (scan done bad : Λ) : Stmt K Λ τ :=
  pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
    (branch (fun v => v.1.getD false)
      (load (fun v => (none, v.2)) (goto (fun _ => scan)))
      (peek src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
        (load (fun v => (none, v.2)) (goto (fun _ => bad)))
        (load (fun v => (none, v.2)) (goto (fun _ => done))))))
    (load (fun v => (none, v.2)) (goto (fun _ => bad))))

/-- Concrete finite decoder machine: three Boolean stacks and finite labels.
The operation labels are returning entry points for subsequent interpreter stages. -/
abbrev machine (n : ℕ) : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 6 ⊕ Op (Fin n)
  main := .inl 0
  State := Option Bool × Unit
  initial := (none, ())
  program
    | .inl i => if i = 0 then fetchStmt 0 (.inl 1) (.inl 4) (.inl 5)
      else if i = 1 then GraphPreprocessing.Frame.scanStmt 0 2 (.inl 1) (.inl 2) (.inl 5)
      else if i = 2 then copyMoveStmt 2 1 (.inl 2) (.inl 3)
      else if i = 3 then opcodeStmt 1 Sum.inr (.inl 5) (labelEncoding n) (n + 6)
      else .halt
    | .inr _ => .halt

/-- True fetch consumes exactly one entry marker and preserves the caller suffix. -/
theorem fetch_cons (n : ℕ) (word suffix : List Bool) :
    (machine n).computer.step (cfg (.inl 0) ()
      (GraphPreprocessing.Frame.tapes (true :: Holant.Algebraic.frame word ++ suffix) [] [])) =
      some (cfg (.inl 1) ()
        (GraphPreprocessing.Frame.tapes (Holant.Algebraic.frame word ++ suffix) [] [])) := by
  simp [machine, FinTM2.step, TM2.step, TM2.stepAux, fetchStmt, cfg,
    GraphPreprocessing.Frame.tapes, Function.update]
  congr 2
  funext k
  fin_cases k <;> rfl

/-- Actual framed fetch, ordered restoration, and finite opcode dispatch. -/
theorem fetch_opcode_exact (n : ℕ) (op : Op (Fin n)) (suffix : List Bool) :
    RunsExactly (machine n).computer.step
      (cfg (.inl 0) () (GraphPreprocessing.Frame.tapes
        (true :: Holant.Algebraic.frame (opEncode (labelEncoding n) op) ++ suffix) [] []))
      (cfg (.inr op) () (GraphPreprocessing.Frame.tapes suffix [] []))
      (2 * (opEncode (labelEncoding n) op).length + 4) := by
  have first := runsExactly_one (fetch_cons n (opEncode (labelEncoding n) op) suffix)
  have second := GraphPreprocessing.Frame.extract_exact (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (machine n).computer.step
    (.inl 1) (.inl 2) (.inl 3) (.inl 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) (opEncode (labelEncoding n) op) suffix []
  simp only [List.append_nil, ← GraphPreprocessing.Frame.tapes_eq] at second
  have last : (machine n).computer.step
      (cfg (.inl 3) () (GraphPreprocessing.Frame.tapes suffix (opEncode (labelEncoding n) op) [])) =
      some (cfg (.inr op) () (GraphPreprocessing.Frame.tapes suffix [] [])) := by
    change some (TM2.stepAux (opcodeStmt 1 Sum.inr (.inl 5) (labelEncoding n) (n + 6))
      (none, ()) (GraphPreprocessing.Frame.tapes suffix (opEncode (labelEncoding n) op) [])) = _
    have hlen := opEncode_length_le (labelEncoding n) n
      (fun i => by simp [labelEncoding]) op
    have h := opcodeStmt_exact (1 : Fin 3) (Sum.inr : Op (Fin n) → Fin 6 ⊕ Op (Fin n))
      (.inl 5) (labelEncoding n) (n + 6) op hlen () (GraphPreprocessing.Frame.tapes suffix [] [])
    have hu : Function.update (GraphPreprocessing.Frame.tapes suffix [] []) 1
        (opEncode (labelEncoding n) op) =
        GraphPreprocessing.Frame.tapes suffix (opEncode (labelEncoding n) op) [] := by
      funext k; fin_cases k <;> rfl
    have hz : Function.update (GraphPreprocessing.Frame.tapes suffix [] []) 1 [] =
        GraphPreprocessing.Frame.tapes suffix [] [] := by
      funext k; fin_cases k <;> rfl
    rw [hu, hz] at h
    exact congrArg some h
  convert (first.trans second).trans (runsExactly_one last) using 1
  omega

/-- The terminating marker is checked and fully removed in one real transition. -/
theorem fetch_done (n : ℕ) :
    (machine n).computer.step
      (cfg (.inl 0) () (GraphPreprocessing.Frame.tapes [false] [] [])) =
      some (cfg (.inl 4) () (GraphPreprocessing.Frame.tapes [] [] [])) := by
  simp [machine, FinTM2.step, TM2.step, TM2.stepAux, fetchStmt, cfg,
    GraphPreprocessing.Frame.tapes, Function.update]
  congr 2
  funext k
  fin_cases k <;> rfl

end Holant.OneHot.StackProgram.Machine.Dispatch
