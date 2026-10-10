import Holant.Complexity.BinaryArithmetic.PairingBits
import Holant.Complexity.BinaryArithmetic.Comparison
import Holant.Complexity.BinaryArithmetic.Multiplication
import Holant.Complexity.BinaryCompose.Embed

/-!
# Finite binary square-shell pairing

The comparison consumes both words while saving their reversals. The selected
shell is copied and squared by the actual multiplier. A real carry-adder computes
the offset in the non-strict branch and the final sum. Each copy, reversal,
comparison, call and cleanup is an ordinary finite TM2 transition.
-/

namespace Holant.Complexity.BinaryArithmetic.Pairing

open Turing Computability BinaryCompose
open Turing.TM2.Stmt

inductive Phase
  | compare | restoreLT | restoreGE | restoreB | saveOffset
  | copyMax | restoreMax | digits | restoreOffset | finish
  deriving DecidableEq
instance : Fintype Phase :=
  ⟨{.compare, .restoreLT, .restoreGE, .restoreB, .saveOffset,
    .copyMax, .restoreMax, .digits, .restoreOffset, .finish}, by intro p; cases p <;> simp⟩

abbrev K := Multiplication.K ⊕ Bool
abbrev Label := Multiplication.Label ⊕ ((Bool × Bool) ⊕ Phase)
abbrev State := Addition.State
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label State
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label State
abbrev initial := Addition.initial
abbrev reset := Addition.reset

def ph (p : Phase) : Label := .inr (.inr p)
def al (final : Bool) (label : Bool) : Label := .inr (.inl (final, label))

def tapes (a b w o m ds ar br : List Bool) : K → List Bool :=
  Sum.elim (Multiplication.tapes a b w o m ds) (Multiplication.extras ar br)

def cfg (label : Option Label) (borrow : Bool) (a b w o m ds ar br : List Bool) : Config :=
  ⟨label, reset borrow, tapes a b w o m ds ar br⟩

def mulLayout (ar br : List Bool) : StackEmbedding Multiplication.K K where
  key := Sum.inl
  lift source := Sum.elim source (Multiplication.extras ar br)
  lookup _ _ := rfl
  update source k word := MachineFrame.update_left source (Multiplication.extras ar br) k word

def mulStates : StateEmbedding Multiplication.Memory State where
  put := Prod.fst
  get v := (v, ())
  get_put v := by rcases v with ⟨v, u⟩; cases u; rfl

def addLayout (m ds ar br : List Bool) : StackEmbedding Addition.Stack K where
  key k := .inl (.inl k)
  lift source := Sum.elim (Sum.elim source (Multiplication.extras m ds)) (Multiplication.extras ar br)
  lookup _ _ := rfl
  update source k word := by
    rw [MachineFrame.update_left, MachineFrame.update_left]

def addStates : StateEmbedding Addition.State State where
  put := id
  get := id
  get_put _ := rfl

def saveFirst (v : State) (bit : Option Bool) : State := (v.1, bit, v.2.2)
def saveSecond (v : State) (bit : Option Bool) : State := (v.1, v.2.1, bit)
def again (p : Phase) : Statement := load (fun _ => initial) (goto (fun _ => ph p))
def finishAt (label : Label) : Statement := load (fun _ => initial) (goto (fun _ => label))
def pushFirst (k : K) (q : Statement) : Statement :=
  branch (fun v => v.2.1.isSome) (push k (fun v => v.2.1.getD false) q) q

def outside : Phase → Statement
  | .compare => pop (.inl (.inl .left)) saveFirst
      (pop (.inl (.inl .right)) saveSecond
        (branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (pushFirst (.inr false)
            (branch (fun v => v.2.2.isSome)
              (push (.inr true) (fun v => v.2.2.getD false)
                (load (fun v => reset (digitBorrow v.1 (v.2.1.getD false) (v.2.2.getD false)))
                  (goto (fun _ => ph .compare))))
              (load (fun v => reset (digitBorrow v.1 (v.2.1.getD false) (v.2.2.getD false)))
                (goto (fun _ => ph .compare)))))
          (branch (fun v => v.1) (again .restoreLT) (again .restoreGE))))
  | .restoreLT => pop (.inr true) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inl (.inr false)) (fun v => v.2.1.getD false)
          (push (.inl (.inl .right)) (fun v => v.2.1.getD false) (again .restoreLT)))
        (again .digits))
  | .restoreGE => pop (.inr false) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inl (.inr false)) (fun v => v.2.1.getD false)
          (push (.inl (.inl .left)) (fun v => v.2.1.getD false) (again .restoreGE)))
        (again .restoreB))
  | .restoreB => pop (.inr true) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inl (.inl .right)) (fun v => v.2.1.getD false) (again .restoreB))
        (finishAt (al false false)))
  | .saveOffset => pop (.inl (.inl .out)) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inr false) (fun v => v.2.1.getD false) (again .saveOffset))
        (again .copyMax))
  | .copyMax => pop (.inl (.inr false)) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inl (.inr true)) (fun v => v.2.1.getD false) (again .copyMax))
        (again .restoreMax))
  | .restoreMax => pop (.inl (.inr true)) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inl (.inr false)) (fun v => v.2.1.getD false)
          (push (.inl (.inl .right)) (fun v => v.2.1.getD false) (again .restoreMax)))
        (again .digits))
  | .digits => pop (.inl (.inl .right)) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inl (.inr true)) (fun v => v.2.1.getD false) (again .digits))
        (finishAt (.inl (.inr .loop))))
  | .restoreOffset => pop (.inr false) saveFirst
      (branch (fun v => v.2.1.isSome)
        (push (.inl (.inl .right)) (fun v => v.2.1.getD false) (again .restoreOffset))
        (finishAt (al true false)))
  | .finish => load (fun _ => initial) halt

def program : Label → Statement
  | .inl label => embedStmt (mulLayout [] []) mulStates Sum.inl (some (ph .restoreOffset))
      (Multiplication.computer.m label)
  | .inr (.inl (final, label)) => embedStmt (addLayout [] [] [] []) addStates (al final)
      (some (ph (if final then .finish else .saveOffset))) (Addition.program label)
  | .inr (.inr phase) => outside phase

abbrev computer : FinTM2 where
  K := K
  k₀ := .inl (.inl .left)
  k₁ := .inl (.inl .out)
  Γ _ := Bool
  Λ := Label
  main := ph .compare
  σ := State
  initialState := initial
  m := program

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

@[simp] theorem update_left (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inl (.inl .left)) x = tapes x b w o m ds ar br := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

@[simp] theorem update_right (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inl (.inl .right)) x = tapes a x w o m ds ar br := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

@[simp] theorem update_work (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inl (.inl .work)) x = tapes a b x o m ds ar br := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

@[simp] theorem update_out (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inl (.inl .out)) x = tapes a b w x m ds ar br := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

@[simp] theorem update_m (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inl (.inr false)) x = tapes a b w o x ds ar br := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

@[simp] theorem update_digits (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inl (.inr true)) x = tapes a b w o m x ar br := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

@[simp] theorem update_ar (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inr false) x = tapes a b w o m ds x br := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

@[simp] theorem update_br (a b w o m ds ar br x : List Bool) :
    Function.update (tapes a b w o m ds ar br) (.inr true) x = tapes a b w o m ds ar x := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, Multiplication.tapes]
    | inr k => cases k <;> simp [tapes, Multiplication.tapes, Multiplication.extras]
  | inr k => cases k <;> simp [tapes, Multiplication.extras]

private theorem embedStmt_layout_eq {S T A B V W : Type} [DecidableEq S] [DecidableEq T]
    (x y : StackEmbedding S T) (h : x.key = y.key) (states : StateEmbedding V W)
    (labels : A → B) (stop : Option B) (q : TM2.Stmt (fun _ : S => Bool) A V) :
    embedStmt x states labels stop q = embedStmt y states labels stop q := by
  induction q <;> simp_all [embedStmt]

/-- The entire multiplier runs on the selected shell, with the saved offset untouched. -/
theorem multiply_exact (m ds ar br : List Bool) :
    Runs (cfg (some (.inl (.inr .loop))) false [] [] [] [] m ds ar br)
      (cfg (some (ph .restoreOffset)) false (MultiplyBits.run m ds []) [] [] [] [] [] ar br)
      (MultiplyBits.time m ds []) := by
  have h := embed_run (mulLayout ar br) mulStates Sum.inl (some (ph .restoreOffset))
    Multiplication.computer.m program (fun label =>
      embedStmt_layout_eq (mulLayout [] []) (mulLayout ar br) rfl _ _ _ _)
    (Multiplication.cfg (some (.inr .loop)) [] [] [] [] m ds)
    (Multiplication.cfg none (MultiplyBits.run m ds []) [] [] [] [] [])
    (MultiplyBits.time m ds []) (Multiplication.run_exact m ds [])
  simpa only [Runs, FinTM2.step, computer, embedCfg, cfg, tapes, mulLayout,
    mulStates, Multiplication.cfg, Multiplication.clean, Option.elim_some, Option.elim_none,
    reset, Addition.reset, initial, Addition.initial] using h

/-- Both addition calls are actual embedded carry-adder executions. -/
theorem addition_exact (final : Bool) (a b m ds ar br : List Bool) :
    Runs (cfg (some (al final false)) false a b [] [] m ds ar br)
      (cfg (some (ph (if final then .finish else .saveOffset))) false
        [] [] [] (addBits false a b) m ds ar br)
      (max a.length b.length + (addBits false a b).length + 2) := by
  have h := embed_run (addLayout m ds ar br) addStates (al final)
    (some (ph (if final then .finish else .saveOffset))) Addition.program program (fun label =>
      embedStmt_layout_eq (addLayout [] [] [] []) (addLayout m ds ar br) rfl _ _ _ _)
    (Addition.cfg (some false) false a b [] [])
    (Addition.cfg none false [] [] [] (addBits false a b))
    _ (Addition.compute_exact false a b)
  simpa only [Runs, FinTM2.step, computer, embedCfg, cfg, tapes, addLayout,
    addStates, Multiplication.tapes, Addition.cfg, Option.elim_some, Option.elim_none,
    reset, Addition.reset, id_eq] using h


@[simp] theorem tapes_a (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inl (.inl .left)) = a := rfl
@[simp] theorem tapes_b (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inl (.inl .right)) = b := rfl
@[simp] theorem tapes_w (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inl (.inl .work)) = w := rfl
@[simp] theorem tapes_o (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inl (.inl .out)) = o := rfl
@[simp] theorem tapes_m (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inl (.inr false)) = m := rfl
@[simp] theorem tapes_ds (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inl (.inr true)) = ds := rfl
@[simp] theorem tapes_ar (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inr false) = ar := rfl
@[simp] theorem tapes_br (a b w o m ds ar br : List Bool) : tapes a b w o m ds ar br (.inr true) = br := rfl

theorem step_compare_both (borrow x y : Bool) (a b ar br : List Bool) :
    computer.step (cfg (some (ph .compare)) borrow (x :: a) (y :: b) [] [] [] [] ar br) =
      some (cfg (some (ph .compare)) (digitBorrow borrow x y) a b [] [] [] [] (x :: ar) (y :: br)) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, saveSecond, again, reset, initial, Addition.reset, Addition.initial,
    pushFirst]
  congr 2

theorem step_compare_left (borrow x : Bool) (a ar br : List Bool) :
    computer.step (cfg (some (ph .compare)) borrow (x :: a) [] [] [] [] [] ar br) =
      some (cfg (some (ph .compare)) (digitBorrow borrow x false) a [] [] [] [] [] (x :: ar) br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, saveSecond, again, reset, initial, Addition.reset, Addition.initial,
    pushFirst]
  congr 2

theorem step_compare_right (borrow y : Bool) (b ar br : List Bool) :
    computer.step (cfg (some (ph .compare)) borrow [] (y :: b) [] [] [] [] ar br) =
      some (cfg (some (ph .compare)) (digitBorrow borrow false y) [] b [] [] [] [] ar (y :: br)) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, saveSecond, again, reset, initial, Addition.reset, Addition.initial,
    pushFirst]
  congr 2

theorem step_compare_nil (borrow : Bool) (ar br : List Bool) :
    computer.step (cfg (some (ph .compare)) borrow [] [] [] [] [] [] ar br) =
      some (cfg (some (ph (if borrow then .restoreLT else .restoreGE))) false [] [] [] [] [] [] ar br) := by
  cases borrow <;>
    simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
      saveFirst, saveSecond, again, reset, initial, Addition.reset, Addition.initial,
      pushFirst] <;> congr 2

/-- Comparison saves both words and counts every scanned column. -/
theorem compare_exact (borrow : Bool) (a b ar br : List Bool) :
    Runs (cfg (some (ph .compare)) borrow a b [] [] [] [] ar br)
      (cfg (some (ph (if (subBits borrow a b).2 then .restoreLT else .restoreGE))) false
        [] [] [] [] [] [] (a.reverse ++ ar) (b.reverse ++ br))
      (max a.length b.length + 1) := by
  induction a generalizing b borrow ar br with
  | nil =>
    induction b generalizing borrow br with
    | nil => simpa [subBits] using Runs.one (step_compare_nil borrow ar br)
    | cons y b ih =>
      have h := (Runs.one (step_compare_right borrow y b ar br)).trans
        (ih (digitBorrow borrow false y) (y :: br))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
  | cons x a ih =>
    cases b with
    | nil =>
      have h := (Runs.one (step_compare_left borrow x a ar br)).trans
        (ih (digitBorrow borrow x false) [] (x :: ar) br)
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
    | cons y b =>
      have h := (Runs.one (step_compare_both borrow x y a b ar br)).trans
        (ih (digitBorrow borrow x y) b (x :: ar) (y :: br))
      simpa [subBits, Nat.succ_max_succ, List.reverse_cons, List.append_assoc] using h

theorem step_restoreLT_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .restoreLT)) false a b w o m ds ar (bit :: br)) =
      some (cfg (some (ph .restoreLT)) false a (bit :: b) w o (bit :: m) ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_restoreLT_nil (a b w o m ds ar : List Bool) :
    computer.step (cfg (some (ph .restoreLT)) false a b w o m ds ar []) =
      some (cfg (some (ph .digits)) false a b w o m ds ar []) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem restoreLT_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .restoreLT)) false a b w o m ds ar br)
      (cfg (some (ph .digits)) false a (br.reverse ++ b) w o (br.reverse ++ m) ds ar []) (br.length + 1) := by
  induction br generalizing b m with
  | nil => simpa using Runs.one (step_restoreLT_nil a b w o m ds ar)
  | cons bit br ih =>
    have h := (Runs.one (step_restoreLT_cons bit a b w o m ds ar br)).trans (ih (bit :: b) (bit :: m))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_restoreGE_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .restoreGE)) false a b w o m ds (bit :: ar) br) =
      some (cfg (some (ph .restoreGE)) false (bit :: a) b w o (bit :: m) ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_restoreGE_nil (a b w o m ds br : List Bool) :
    computer.step (cfg (some (ph .restoreGE)) false a b w o m ds [] br) =
      some (cfg (some (ph .restoreB)) false a b w o m ds [] br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem restoreGE_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .restoreGE)) false a b w o m ds ar br)
      (cfg (some (ph .restoreB)) false (ar.reverse ++ a) b w o (ar.reverse ++ m) ds [] br) (ar.length + 1) := by
  induction ar generalizing a m with
  | nil => simpa using Runs.one (step_restoreGE_nil a b w o m ds br)
  | cons bit ar ih =>
    have h := (Runs.one (step_restoreGE_cons bit a b w o m ds ar br)).trans (ih (bit :: a) (bit :: m))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_restoreB_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .restoreB)) false a b w o m ds ar (bit :: br)) =
      some (cfg (some (ph .restoreB)) false a (bit :: b) w o m ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, al, cfg, TM2.stepAux,
    saveFirst, again, finishAt, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_restoreB_nil (a b w o m ds ar : List Bool) :
    computer.step (cfg (some (ph .restoreB)) false a b w o m ds ar []) =
      some (cfg (some (al false false)) false a b w o m ds ar []) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, al, cfg, TM2.stepAux,
    saveFirst, again, finishAt, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem restoreB_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .restoreB)) false a b w o m ds ar br)
      (cfg (some (al false false)) false a (br.reverse ++ b) w o m ds ar []) (br.length + 1) := by
  induction br generalizing b with
  | nil => simpa using Runs.one (step_restoreB_nil a b w o m ds ar)
  | cons bit br ih =>
    have h := (Runs.one (step_restoreB_cons bit a b w o m ds ar br)).trans (ih (bit :: b))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_saveOffset_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .saveOffset)) false a b w (bit :: o) m ds ar br) =
      some (cfg (some (ph .saveOffset)) false a b w o m ds (bit :: ar) br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_saveOffset_nil (a b w m ds ar br : List Bool) :
    computer.step (cfg (some (ph .saveOffset)) false a b w [] m ds ar br) =
      some (cfg (some (ph .copyMax)) false a b w [] m ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem saveOffset_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .saveOffset)) false a b w o m ds ar br)
      (cfg (some (ph .copyMax)) false a b w [] m ds (o.reverse ++ ar) br) (o.length + 1) := by
  induction o generalizing ar with
  | nil => simpa using Runs.one (step_saveOffset_nil a b w m ds ar br)
  | cons bit o ih =>
    have h := (Runs.one (step_saveOffset_cons bit a b w o m ds ar br)).trans (ih (bit :: ar))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_copyMax_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .copyMax)) false a b w o (bit :: m) ds ar br) =
      some (cfg (some (ph .copyMax)) false a b w o m (bit :: ds) ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_copyMax_nil (a b w o ds ar br : List Bool) :
    computer.step (cfg (some (ph .copyMax)) false a b w o [] ds ar br) =
      some (cfg (some (ph .restoreMax)) false a b w o [] ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem copyMax_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .copyMax)) false a b w o m ds ar br)
      (cfg (some (ph .restoreMax)) false a b w o [] (m.reverse ++ ds) ar br) (m.length + 1) := by
  induction m generalizing ds with
  | nil => simpa using Runs.one (step_copyMax_nil a b w o ds ar br)
  | cons bit m ih =>
    have h := (Runs.one (step_copyMax_cons bit a b w o m ds ar br)).trans (ih (bit :: ds))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_restoreMax_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .restoreMax)) false a b w o m (bit :: ds) ar br) =
      some (cfg (some (ph .restoreMax)) false a (bit :: b) w o (bit :: m) ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_restoreMax_nil (a b w o m ar br : List Bool) :
    computer.step (cfg (some (ph .restoreMax)) false a b w o m [] ar br) =
      some (cfg (some (ph .digits)) false a b w o m [] ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem restoreMax_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .restoreMax)) false a b w o m ds ar br)
      (cfg (some (ph .digits)) false a (ds.reverse ++ b) w o (ds.reverse ++ m) [] ar br) (ds.length + 1) := by
  induction ds generalizing b m with
  | nil => simpa using Runs.one (step_restoreMax_nil a b w o m ar br)
  | cons bit ds ih =>
    have h := (Runs.one (step_restoreMax_cons bit a b w o m ds ar br)).trans (ih (bit :: b) (bit :: m))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_digits_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .digits)) false a (bit :: b) w o m ds ar br) =
      some (cfg (some (ph .digits)) false a b w o m (bit :: ds) ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, finishAt, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_digits_nil (a w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .digits)) false a [] w o m ds ar br) =
      some (cfg (some (.inl (.inr .loop))) false a [] w o m ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    saveFirst, again, finishAt, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem digits_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .digits)) false a b w o m ds ar br)
      (cfg (some (.inl (.inr .loop))) false a [] w o m (b.reverse ++ ds) ar br) (b.length + 1) := by
  induction b generalizing ds with
  | nil => simpa using Runs.one (step_digits_nil a w o m ds ar br)
  | cons bit b ih =>
    have h := (Runs.one (step_digits_cons bit a b w o m ds ar br)).trans (ih (bit :: ds))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_restoreOffset_cons (bit : Bool) (a b w o m ds ar br : List Bool) :
    computer.step (cfg (some (ph .restoreOffset)) false a b w o m ds (bit :: ar) br) =
      some (cfg (some (ph .restoreOffset)) false a (bit :: b) w o m ds ar br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, al, cfg, TM2.stepAux,
    saveFirst, again, finishAt, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem step_restoreOffset_nil (a b w o m ds br : List Bool) :
    computer.step (cfg (some (ph .restoreOffset)) false a b w o m ds [] br) =
      some (cfg (some (al true false)) false a b w o m ds [] br) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, al, cfg, TM2.stepAux,
    saveFirst, again, finishAt, reset, initial, Addition.reset, Addition.initial]
  congr 2

theorem restoreOffset_exact (a b w o m ds ar br : List Bool) :
    Runs (cfg (some (ph .restoreOffset)) false a b w o m ds ar br)
      (cfg (some (al true false)) false a (ar.reverse ++ b) w o m ds [] br) (ar.length + 1) := by
  induction ar generalizing b with
  | nil => simpa using Runs.one (step_restoreOffset_nil a b w o m ds br)
  | cons bit ar ih =>
    have h := (Runs.one (step_restoreOffset_cons bit a b w o m ds ar br)).trans (ih (bit :: b))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem step_finish (o : List Bool) :
    computer.step (cfg (some (ph .finish)) false [] [] [] o [] [] [] []) =
      some (cfg none false [] [] [] o [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, outside, ph, cfg, TM2.stepAux,
    reset, initial, Addition.reset, Addition.initial]
  congr 2


def addTime (a b : List Bool) : ℕ := max a.length b.length + (addBits false a b).length + 2

def finishTime (m offset : List Bool) : ℕ :=
  MultiplyBits.time m m.reverse [] + (offset.length + 1) +
    addTime (MultiplyBits.run m m.reverse []) offset + 1

/-- Square the chosen shell, restore its saved offset and add; scratch is empty. -/
theorem finish_exact (m offset : List Bool) :
    Runs (cfg (some (.inl (.inr .loop))) false [] [] [] [] m m.reverse offset.reverse [])
      (cfg none false [] [] [] (addBits false (MultiplyBits.run m m.reverse []) offset) [] [] [] [])
      (finishTime m offset) := by
  have h₁ := multiply_exact m m.reverse offset.reverse []
  have h₂ := restoreOffset_exact (MultiplyBits.run m m.reverse []) [] [] [] [] [] offset.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₂
  have h₃ := addition_exact true (MultiplyBits.run m m.reverse []) offset [] [] [] []
  simp only [ ↓reduceIte] at h₃
  have h₄ := Runs.one (step_finish (addBits false (MultiplyBits.run m m.reverse []) offset))
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  convert h using 1
  unfold finishTime addTime
  omega

/-- The strict branch prepares b*b+a with two full word transfers. -/
theorem prepareLT_exact (a b : List Bool) :
    Runs (cfg (some (ph .restoreLT)) false [] [] [] [] [] [] a.reverse b.reverse)
      (cfg (some (.inl (.inr .loop))) false [] [] [] [] b b.reverse a.reverse [])
      (2 * (b.length + 1)) := by
  have h₁ := restoreLT_exact [] [] [] [] [] [] a.reverse b.reverse
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₁
  have h₂ := digits_exact [] b [] [] b [] a.reverse []
  simp only [List.append_nil] at h₂
  have h := h₁.trans h₂
  convert h using 1
  omega

/-- The other branch computes the offset a+b and physically copies a for squaring. -/
theorem prepareGE_exact (a b : List Bool) :
    Runs (cfg (some (ph .restoreGE)) false [] [] [] [] [] [] a.reverse b.reverse)
      (cfg (some (.inl (.inr .loop))) false [] [] [] [] a a.reverse (addBits false a b).reverse [])
      (4 * (a.length + 1) + (b.length + 1) + addTime a b + (addBits false a b).length + 1) := by
  have h₁ := restoreGE_exact [] [] [] [] [] [] a.reverse b.reverse
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₁
  have h₂ := restoreB_exact a [] [] [] a [] [] b.reverse
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₂
  have h₃ := addition_exact false a b a [] [] []
  simp only [Bool.false_eq_true, ↓reduceIte] at h₃
  have h₄ := saveOffset_exact [] [] [] (addBits false a b) a [] [] []
  simp only [List.append_nil] at h₄
  have h₅ := copyMax_exact [] [] [] [] a [] (addBits false a b).reverse []
  simp only [List.append_nil] at h₅
  have h₆ := restoreMax_exact [] [] [] [] [] a.reverse (addBits false a b).reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₆
  have h₇ := digits_exact [] a [] [] a [] (addBits false a b).reverse []
  simp only [List.append_nil] at h₇
  have h := (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇
  convert h using 1
  unfold addTime
  omega

/-- Exact transition count; natural arithmetic occurs only in this specification. -/
def time (a b : ℕ) : ℕ :=
  max (encodeNat a).length (encodeNat b).length + 1 +
    if a < b then
      2 * ((encodeNat b).length + 1) + finishTime (encodeNat b) (encodeNat a)
    else
      4 * ((encodeNat a).length + 1) + ((encodeNat b).length + 1) +
        addTime (encodeNat a) (encodeNat b) + (encodeNat (a + b)).length + 1 +
        finishTime (encodeNat a) (encodeNat (a + b))

/-- Both branches return the literal canonical encoding of mathlib's Nat.pair. -/
theorem compute_encodeNat_exact (a b : ℕ) :
    Runs (cfg (some (ph .compare)) false (encodeNat a) (encodeNat b) [] [] [] [] [] [])
      (cfg none false [] [] [] (encodeNat (Nat.pair a b)) [] [] [] []) (time a b) := by
  have hc := compare_exact false (encodeNat a) (encodeNat b) [] []
  simp only [Comparison.borrow_encodeNat, List.append_nil, decide_eq_true_eq] at hc
  by_cases hab : a < b
  · simp only [hab, ↓reduceIte] at hc
    have hp := prepareLT_exact (encodeNat a) (encodeNat b)
    have hf := finish_exact (encodeNat b) (encodeNat a)
    rw [MultiplyBits.run_encodeNat, addBits_encodeNat] at hf
    have h := (hc.trans hp).trans hf
    rw [Nat.pair, ite_eq_left hab]
    convert h using 1
    simp only [time, hab, ↓reduceIte]
    omega
  · simp only [hab, ↓reduceIte] at hc
    have hp := prepareGE_exact (encodeNat a) (encodeNat b)
    rw [addBits_encodeNat] at hp
    have hf := finish_exact (encodeNat a) (encodeNat (a + b))
    rw [MultiplyBits.run_encodeNat, addBits_encodeNat, ← Nat.add_assoc] at hf
    have h := (hc.trans hp).trans hf
    rw [Nat.pair, ite_eq_right hab]
    convert h using 1
    simp only [time, hab, ↓reduceIte]
    omega

/-- Compatibility with the bitwise pairing specification, not merely decoding. -/
theorem compute_pairBits_exact (a b : ℕ) :
    Runs (cfg (some (ph .compare)) false (encodeNat a) (encodeNat b) [] [] [] [] [] [])
      (cfg none false [] [] [] (PairingBits.pairBits (encodeNat a) (encodeNat b)) [] [] [] [])
      (time a b) := by
  rw [PairingBits.pairBits_encodeNat]
  exact compute_encodeNat_exact a b


/-- A word-length bound derived from the bitwise multiplication recurrence. -/
theorem product_length_le (m digits a : List Bool) :
    (MultiplyBits.run m digits a).length ≤ a.length + digits.length * (m.length + 2) := by
  induction digits generalizing a with
  | nil => simp [MultiplyBits.run]
  | cons bit digits ih =>
    have h := ih (MultiplyBits.next bit m a)
    have hn := MultiplyBits.next_length_le bit m a
    simp only [MultiplyBits.run, List.length_cons]
    nlinarith

theorem addTime_le (a b : List Bool) : addTime a b ≤ 2 * max a.length b.length + 3 := by
  have h := addBits_length_le false a b
  unfold addTime
  omega

/-- A concrete uniform cubic bound for the square-and-offset suffix. -/
theorem finishTime_le (m offset : List Bool) (N : ℕ)
    (hm : m.length ≤ N) (ho : offset.length ≤ N + 1) :
    finishTime m offset ≤
      (N + 1) * (6 * ((N + 1) * (N + 2) + 3)) + 2 * ((N + 1) * (N + 2)) + N + 6 := by
  have ht := MultiplyBits.time_le m m.reverse []
  simp only [List.length_reverse, List.length_nil, Nat.zero_add] at ht
  have hp : (m.length + 1) * (m.length + 2) ≤ (N + 1) * (N + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmul : MultiplyBits.time m m.reverse [] ≤
      (N + 1) * (6 * ((N + 1) * (N + 2) + 3)) :=
    ht.trans (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 6 (Nat.add_le_add_right hp 3)))
  have hs := product_length_le m m.reverse []
  simp only [List.length_reverse, List.length_nil, Nat.zero_add] at hs
  have hp' : m.length * (m.length + 2) ≤ (N + 1) * (N + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have ho' : offset.length ≤ (N + 1) * (N + 2) := by nlinarith
  have hmax : max (MultiplyBits.run m m.reverse []).length offset.length ≤
      (N + 1) * (N + 2) := max_le (hs.trans hp') ho'
  have ha := addTime_le (MultiplyBits.run m m.reverse []) offset
  unfold finishTime
  omega

/-- Prepared computation is polynomial in any upper bound on the two bit lengths. -/
theorem time_le (a b N : ℕ) (ha : (encodeNat a).length ≤ N) (hb : (encodeNat b).length ≤ N) :
    time a b ≤
      (N + 1) * (6 * ((N + 1) * (N + 2) + 3)) + 2 * ((N + 1) * (N + 2)) + 10 * N + 20 := by
  have hab : max (encodeNat a).length (encodeNat b).length ≤ N := max_le ha hb
  have hsum := addBits_length_le false (encodeNat a) (encodeNat b)
  rw [addBits_encodeNat] at hsum
  have ha' := addTime_le (encodeNat a) (encodeNat b)
  unfold time
  split
  · have hf := finishTime_le (encodeNat b) (encodeNat a) N hb (by omega)
    omega
  · have hf := finishTime_le (encodeNat a) (encodeNat (a + b)) N ha (by omega)
    omega

/-- Prepared-stack timed execution, including comparison, copies and clean halt. -/
def compute_timed (a b : ℕ) :
    StateTransition.EvalsToInTime computer.step
      (cfg (some (ph .compare)) false (encodeNat a) (encodeNat b) [] [] [] [] [] [])
      (some (cfg none false [] [] [] (encodeNat (Nat.pair a b)) [] [] [] []))
      (let N := max (encodeNat a).length (encodeNat b).length
       (N + 1) * (6 * ((N + 1) * (N + 2) + 3)) + 2 * ((N + 1) * (N + 2)) + 10 * N + 20) where
  steps := time a b
  evals_in_steps := compute_encodeNat_exact a b
  steps_le_m := time_le a b _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem outside_budget (phase : Phase) : TM2Cost.budget (outside phase) ≤ 9 := by
  cases phase <;> decide

/-- The structural arithmetic embeddings preserve their primitive budgets. -/
theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 9 := by
  cases label with
  | inl label =>
    simp only [computer, program, embed_budget]
    exact le_trans (Multiplication.program_budget label) (by decide)
  | inr label => cases label with
    | inl label =>
      rcases label with ⟨final, label⟩
      simp only [computer, program, embed_budget]
      exact le_trans (Addition.program_budget label) (by decide)
    | inr phase => exact outside_budget phase

@[simp] theorem stack_count : Fintype.card computer.K = 8 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 22 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.Pairing
