import Holant.OneHot.StackProgram.Machine.Dispatch
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Complexity.GraphPreprocessing.Primitive

/-! Real finite-control recoding of fixed finite label/assignment alphabets. The
input decision tree is statically unrolled to a proved fixed width. Each output
word compiles into literal Boolean pushes at a finite control label. This is not
an unbounded lookup, field-arithmetic operation or graph-processing callback. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.Complexity.GraphPreprocessing.FiniteRecode

open Turing Computability BinaryCompose StackProtocol
open Holant.OneHot.StackProgram.Machine.Dispatch
variable {A B : Type} [Fintype A]

def leaf (e : Encoding A Bool) (bits : List Bool) : Bool ⊕ A :=
  (e.decode bits).elim (.inl true) Sum.inr

/-- Two actual transitions, each with a separate fixed primitive-syntax bound. -/
abbrev machine (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B) (C : ℕ) : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Bool ⊕ A
  main := .inl false
  State := Option Bool × Unit
  initial := (none, ())
  program
    | .inl false => decodeStmt () (leaf ea) (.inl true) C []
    | .inl true => .halt
    | .inr a => FixedFieldMachines.Constant.pushWord () (eb.encode (f a)) .halt

private theorem update_empty (word : List Bool) :
    Function.update (wordTape () []) () word = wordTape () word := by
  funext k
  cases k
  rfl

/-- Exact faithful input decoding, clearing the original input stack. -/
theorem decode_step (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B)
    (C : ℕ) (a : A) (ha : (ea.encode a).length ≤ C) :
    (machine ea eb f C).computer.step (initList (machine ea eb f C).computer (ea.encode a)) =
      some (cfg (.inr a) () (wordTape () [])) := by
  rw [Machine.init_eq]
  change some (TM2.stepAux (decodeStmt () (leaf ea) (.inl true) C [])
    (none, ()) (wordTape () (ea.encode a))) = _
  have h := decodeStmt_exact () (leaf ea) (.inl true) C [] (ea.encode a) ha
    (none, ()) (wordTape () [])
  rw [update_empty, update_empty] at h
  simpa [leaf] using congrArg some h

/-- The decoded fixed table entry is emitted by real push syntax, not a load-word primitive. -/
theorem output_step (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B)
    (C : ℕ) (a : A) :
    (machine ea eb f C).computer.step (cfg (.inr a) () (wordTape () [])) =
      some (haltList (machine ea eb f C).computer (eb.encode (f a))) := by
  rw [Machine.halt_eq]
  change some (TM2.stepAux (FixedFieldMachines.Constant.pushWord () (eb.encode (f a)) .halt)
    (none, ()) (wordTape () [])) = _
  rw [FixedFieldMachines.Constant.pushWord_eval]
  simp [TM2.stepAux, wordTape, Function.update_idem]

theorem exact_run (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B)
    (C : ℕ) (hc : ∀ a, (ea.encode a).length ≤ C) (a : A) :
    RunsExactly (machine ea eb f C).computer.step
      (initList (machine ea eb f C).computer (ea.encode a))
      (haltList (machine ea eb f C).computer (eb.encode (f a))) 2 :=
  (runsExactly_one (decode_step ea eb f C a (hc a))).trans
    (runsExactly_one (output_step ea eb f C a))

/-- The input alphabet and all labels/registers are genuinely finite. This
microprogram only recodes a fixed finite label domain, not an arbitrary graph. -/
noncomputable def computes (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B)
    (C : ℕ) (hc : ∀ a, (ea.encode a).length ≤ C) : Computes ea eb f where
  machine := machine ea eb f C
  time := 2
  outputs a := {
    steps := 2
    evals_in_steps := exact_run ea eb f C hc a
    steps_le_m := by simp }

/-- All popped bits, branch tests, output bits and terminal control are charged. -/
theorem program_budget (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B)
    (C D : ℕ) (hd : ∀ a, (eb.encode (f a)).length ≤ D) (label : Bool ⊕ A) :
    TM2Cost.budget ((machine ea eb f C).program label) ≤ 3 * C + D + 4 := by
  cases label with
  | inl flag =>
    cases flag with
    | false => exact (decodeStmt_budget () (leaf ea) (.inl true) C []).trans (by omega)
    | true => simp [machine, TM2Cost.budget]
  | inr a =>
    have h := hd a
    simp only [machine, FixedFieldMachines.Constant.pushWord_budget, TM2Cost.budget]
    omega

/-- Actual accumulated primitive cost of the SAME clean recoding execution. -/
theorem primitive_cost (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B)
    (C D : ℕ) (hc : ∀ a, (ea.encode a).length ≤ C)
    (hd : ∀ a, (eb.encode (f a)).length ≤ D) (a : A) :
    (Primitive.run (machine ea eb f C).program 2
      (some (initList (machine ea eb f C).computer (ea.encode a)))).2 =
        some (haltList (machine ea eb f C).computer (eb.encode (f a))) ∧
    (Primitive.run (machine ea eb f C).program 2
      (some (initList (machine ea eb f C).computer (ea.encode a)))).1 ≤
          2 * (3 * C + D + 4) := by
  have h := Primitive.execution_cost (machine ea eb f C).program (3 * C + D + 4)
    (program_budget ea eb f C D hd) 2 _ _ (exact_run ea eb f C hc a)
  simpa [Nat.mul_comm] using h

end Holant.Complexity.GraphPreprocessing.FiniteRecode
