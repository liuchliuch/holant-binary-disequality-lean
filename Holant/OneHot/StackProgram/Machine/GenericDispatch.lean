import Holant.OneHot.StackProgram.Machine.Dispatch

/-! Generic finite coefficient labels are retained literally. A fixed explicit
Boolean label dictionary with a proved length bound suffices; no conversion to
Fin or runtime coefficient-value search is used. -/
namespace Holant.OneHot.StackProgram.Machine.GenericDispatch
open Turing Computability Holant.Complexity StackProtocol
open Holant.OneHot.StackProgram.Machine.Dispatch
variable {A : Type} [Fintype A]

/-- Concrete finite decoder machine: three Boolean stacks and original finite labels.
The operation labels are returning entry points for subsequent interpreter stages. -/
abbrev machine (e : Encoding A Bool) (C : ℕ) : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 6 ⊕ Op A
  main := .inl 0
  State := Option Bool × Unit
  initial := (none, ())
  program
    | .inl i => if i = 0 then fetchStmt 0 (.inl 1) (.inl 4) (.inl 5)
      else if i = 1 then GraphPreprocessing.Frame.scanStmt 0 2 (.inl 1) (.inl 2) (.inl 5)
      else if i = 2 then copyMoveStmt 2 1 (.inl 2) (.inl 3)
      else if i = 3 then opcodeStmt 1 Sum.inr (.inl 5) e (C + 6)
      else .halt
    | .inr _ => .halt

/-- True fetch consumes exactly one entry marker and preserves the caller suffix. -/
theorem fetch_cons (e : Encoding A Bool) (C : ℕ) (word suffix : List Bool) :
    (machine e C).computer.step (cfg (.inl 0) ()
      (GraphPreprocessing.Frame.tapes (true :: Holant.Algebraic.frame word ++ suffix) [] [])) =
      some (cfg (.inl 1) ()
        (GraphPreprocessing.Frame.tapes (Holant.Algebraic.frame word ++ suffix) [] [])) := by
  simp [machine, FinTM2.step, TM2.step, TM2.stepAux, fetchStmt, cfg,
    GraphPreprocessing.Frame.tapes, Function.update]
  congr 2
  funext k
  fin_cases k <;> rfl

/-- Actual framed fetch, ordered restoration, and finite opcode dispatch. -/
theorem fetch_opcode_exact (e : Encoding A Bool) (C : ℕ)
    (hlabels : ∀ a, (e.encode a).length ≤ C) (op : Op A) (suffix : List Bool) :
    RunsExactly (machine e C).computer.step
      (cfg (.inl 0) () (GraphPreprocessing.Frame.tapes
        (true :: Holant.Algebraic.frame (opEncode e op) ++ suffix) [] []))
      (cfg (.inr op) () (GraphPreprocessing.Frame.tapes suffix [] []))
      (2 * (opEncode e op).length + 4) := by
  have first := runsExactly_one (fetch_cons e C (opEncode e op) suffix)
  have second := GraphPreprocessing.Frame.extract_exact (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (machine e C).computer.step
    (.inl 1) (.inl 2) (.inl 3) (.inl 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) (opEncode e op) suffix []
  simp only [List.append_nil, ← GraphPreprocessing.Frame.tapes_eq] at second
  have last : (machine e C).computer.step
      (cfg (.inl 3) () (GraphPreprocessing.Frame.tapes suffix (opEncode e op) [])) =
      some (cfg (.inr op) () (GraphPreprocessing.Frame.tapes suffix [] [])) := by
    change some (TM2.stepAux (opcodeStmt 1 Sum.inr (.inl 5) e (C + 6))
      (none, ()) (GraphPreprocessing.Frame.tapes suffix (opEncode e op) [])) = _
    have hlen := opEncode_length_le e C hlabels op
    have h := opcodeStmt_exact (1 : Fin 3) (Sum.inr : Op A → Fin 6 ⊕ Op A)
      (.inl 5) e (C + 6) op hlen () (GraphPreprocessing.Frame.tapes suffix [] [])
    have hu : Function.update (GraphPreprocessing.Frame.tapes suffix [] []) 1
        (opEncode e op) =
        GraphPreprocessing.Frame.tapes suffix (opEncode e op) [] := by
      funext k; fin_cases k <;> rfl
    have hz : Function.update (GraphPreprocessing.Frame.tapes suffix [] []) 1 [] =
        GraphPreprocessing.Frame.tapes suffix [] [] := by
      funext k; fin_cases k <;> rfl
    rw [hu, hz] at h
    exact congrArg some h
  convert (first.trans second).trans (runsExactly_one last) using 1
  omega

/-- The terminating marker is checked and fully removed in one real transition. -/
theorem fetch_done (e : Encoding A Bool) (C : ℕ) :
    (machine e C).computer.step
      (cfg (.inl 0) () (GraphPreprocessing.Frame.tapes [false] [] [])) =
      some (cfg (.inl 4) () (GraphPreprocessing.Frame.tapes [] [] [])) := by
  simp [machine, FinTM2.step, TM2.step, TM2.stepAux, fetchStmt, cfg,
    GraphPreprocessing.Frame.tapes, Function.update]
  congr 2
  funext k
  fin_cases k <;> rfl


end Holant.OneHot.StackProgram.Machine.GenericDispatch
