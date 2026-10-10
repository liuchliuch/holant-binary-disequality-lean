import Holant.Complexity.RationalArithmetic.NormalizeBits
import Holant.Complexity.RationalArithmetic.Call
import Holant.Complexity.RationalArithmetic.Protocol
import Holant.Complexity.BinaryArithmetic.Gcd
import Mathlib.Tactic.Linarith
import Holant.Complexity.BinaryCompose.Interface

/-! Canonical fraction normalization by actual binary gcd and two actual
quotient calls. Every copy, reversal, carry, borrow and cleanup is a finite
Boolean-stack loop. The clean output is the established framed natural pair of
integer numerator code and denominator, ready for the exact pairing machine. -/
namespace Holant.Complexity.RationalArithmetic.Normalization
open Turing Computability BinaryArithmetic IntegerArithmetic BinaryCompose
open Turing.TM2.Stmt

inductive Extra
  | num | den | temp | gcd | stream
  deriving DecidableEq
instance : Fintype Extra := ⟨{.num, .den, .temp, .gcd, .stream}, by intro x; cases x <;> simp⟩

inductive Phase
  | first | second | sign | inc | restoreInc | start | zeroClear | zeroDen
  | copyN | restoreN | reverseN | copyD | restoreD
  | moveG | splitG | numerator | saveN | restoreQN | moveSavedG | restoreG
  | denominator | callD | saveD | restoreQD
  | recode | dec | restoreDec | tag | packD | delimiter | packN
  deriving DecidableEq
instance : Fintype Phase := ⟨{.first, .second, .sign, .inc, .restoreInc, .start, .zeroClear, .zeroDen,
  .copyN, .restoreN, .reverseN, .copyD, .restoreD, .moveG, .splitG, .numerator, .saveN,
  .restoreQN, .moveSavedG, .restoreG, .denominator, .callD, .saveD, .restoreQD,
  .recode, .dec, .restoreDec, .tag, .packD, .delimiter, .packN}, by intro x; cases x <;> simp⟩

abbrev K := Gcd.Stack ⊕ Extra
abbrev QL := Division.Label ⊕ Empty
abbrev Label := Gcd.Label ⊕ (QL ⊕ Phase)
abbrev Memory := CarryProtocol.Memory
abbrev Config := CarryProtocol.Config K Label
abbrev Statement := CarryProtocol.Statement K Label
abbrev ph (p : Phase) : Label := .inr (.inr p)
abbrev ql (p : QL) : Label := .inr (.inl p)
abbrev dl (p : Division.Label) : Label := ql (.inl p)
abbrev sk (p : Division.Stack) : K := .inl (.inl p)
abbrev ex (p : Extra) : K := .inr p

def layout (frame : Extra → List Bool) : StackEmbedding Gcd.Stack K where
  key := Sum.inl
  lift source := Sum.elim source frame
  lookup _ _ := rfl
  update source k word := MachineFrame.update_left source frame k word

def quotientProgram : QL → TM2.Stmt (fun _ : Gcd.Stack => Bool) QL Gcd.Memory :=
  MachineFrame.program (Division.program false) Empty.elim

def gcdReturn (_ : CarryProtocol.Signs) : Label := ph .moveG
def quotientReturn (s : CarryProtocol.Signs) : Label := ph (if s.2 then .saveD else .saveN)
def again (p : Label) : Statement := load CarryProtocol.clearBit (goto (fun _ => p))
def move (src dst : K) (loop next : Label) : Statement :=
  CarryProtocol.restoreStmt dst src loop (fun _ => next)

/-- The only callbacks inspect finite optional bits or saved Boolean signs. -/
def outside : Phase → Statement
  | .first => pop (ex .stream) CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.getD false)
        (pop (ex .stream) CarryProtocol.saveBit
          (push (ex .num) (fun v => v.1.1.2.1.getD false) (again (ph .first))))
        (again (ph .second)))
  | .second => pop (ex .stream) CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (push (ex .den) (fun v => v.1.1.2.1.getD false) (again (ph .second)))
        (again (ph .sign)))
  | .sign => pop (ex .num) (fun v bit => (v.1, (bit.getD false, false)))
      (goto (fun v => ph (if v.2.1 then .inc else .start)))
  | .inc => CarryProtocol.incrementStmt (ex .num) (ex .temp) (ph .inc) (ph .restoreInc)
  | .restoreInc => CarryProtocol.restoreStmt (ex .num) (ex .temp) (ph .restoreInc) (fun _ => ph .start)
  | .start => peek (ex .den) CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome) (again (ph .copyN)) (again (ph .zeroClear)))
  | .zeroClear => NormalizeProtocol.clearStmt (ex .num) (ph .zeroClear) (fun _ => ph .zeroDen)
  | .zeroDen => push (ex .den) (fun _ => true) (again (ph .packD))
  | .copyN => move (ex .num) (ex .temp) (ph .copyN) (ph .restoreN)
  | .restoreN => Protocol.splitStmt (ex .num) (sk .divisorRev) (ex .temp) (ph .restoreN) (ph .reverseN)
  | .reverseN => move (sk .divisorRev) (sk .input) (ph .reverseN) (ph .copyD)
  | .copyD => move (ex .den) (ex .temp) (ph .copyD) (ph .restoreD)
  | .restoreD => Protocol.splitStmt (ex .den) (sk .divisor) (ex .temp) (ph .restoreD) (.inl (.inr .loop))
  | .moveG => move (sk .remainder) (ex .temp) (ph .moveG) (ph .splitG)
  | .splitG => Protocol.splitStmt (ex .gcd) (sk .divisor) (ex .temp) (ph .splitG) (ph .numerator)
  | .numerator => move (ex .num) (sk .input) (ph .numerator) (dl .start)
  | .saveN => move (sk .quotient) (ex .temp) (ph .saveN) (ph .restoreQN)
  | .restoreQN => move (ex .temp) (ex .num) (ph .restoreQN) (ph .moveSavedG)
  | .moveSavedG => move (ex .gcd) (ex .temp) (ph .moveSavedG) (ph .restoreG)
  | .restoreG => move (ex .temp) (sk .divisor) (ph .restoreG) (ph .denominator)
  | .denominator => move (ex .den) (sk .input) (ph .denominator) (ph .callD)
  | .callD => load (fun v => CarryProtocol.clean (v.2.1, true)) (goto (fun _ => dl .start))
  | .saveD => move (sk .quotient) (ex .temp) (ph .saveD) (ph .restoreQD)
  | .restoreQD => move (ex .temp) (ex .den) (ph .restoreQD) (ph .recode)
  | .recode => peek (ex .num) CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (branch (fun v => v.2.1) (again (ph .dec))
          (push (ex .num) (fun _ => false) (again (ph .packD))))
        (again (ph .packD)))
  | .dec => CarryProtocol.decrementStmt (ex .num) (ex .temp) (ph .dec) (ph .restoreDec)
  | .restoreDec => CarryProtocol.restoreStmt (ex .num) (ex .temp) (ph .restoreDec) (fun _ => ph .tag)
  | .tag => push (ex .num) (fun _ => true) (again (ph .packD))
  | .packD => move (ex .den) (ex .stream) (ph .packD) (ph .delimiter)
  | .delimiter => push (ex .stream) (fun _ => false) (again (ph .packN))
  | .packN => pop (ex .num) CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (push (ex .stream) (fun v => v.1.1.2.1.getD false)
          (push (ex .stream) (fun _ => true) (again (ph .packN))))
        (load (fun _ => CarryProtocol.clean (false, false)) halt))

def program : Label → Statement
  | .inl l => Call.stmt (layout (fun _ => [])) Sum.inl gcdReturn (Gcd.computer.m l)
  | .inr (.inl l) => Call.stmt (layout (fun _ => [])) ql quotientReturn (quotientProgram l)
  | .inr (.inr p) => outside p

abbrev computer : FinTM2 where
  K := K
  k₀ := ex .stream
  k₁ := ex .stream
  Γ _ := Bool
  Λ := Label
  main := ph .first
  σ := Memory
  initialState := CarryProtocol.clean (false, false)
  m := program
instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

structure Data where
  i : List Bool := []
  d : List Bool := []
  r : List Bool := []
  dr : List Bool := []
  old : List Bool := []
  trial : List Bool := []
  q : List Bool := []
  saved : List Bool := []
  gtemp : List Bool := []
  n : List Bool := []
  e : List Bool := []
  t : List Bool := []
  g : List Bool := []
  s : List Bool := []

def Data.frame (w : Data) : Extra → List Bool
  | .num => w.n
  | .den => w.e
  | .temp => w.t
  | .gcd => w.g
  | .stream => w.s

def Data.source (w : Data) : Gcd.Stack → List Bool :=
  Sum.elim (Division.tapes w.i w.d w.r w.dr w.old w.trial w.q) (Gcd.frame w.saved w.gtemp)

def Data.tapes (w : Data) : K → List Bool := Sum.elim w.source w.frame

@[simp] theorem Data.lookup_i (w : Data) : w.tapes (sk .input) = w.i := rfl
@[simp] theorem Data.update_i (w : Data) (x : List Bool) :
    Function.update w.tapes (sk .input) x = ({w with i := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_d (w : Data) : w.tapes (sk .divisor) = w.d := rfl
@[simp] theorem Data.update_d (w : Data) (x : List Bool) :
    Function.update w.tapes (sk .divisor) x = ({w with d := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_r (w : Data) : w.tapes (sk .remainder) = w.r := rfl
@[simp] theorem Data.update_r (w : Data) (x : List Bool) :
    Function.update w.tapes (sk .remainder) x = ({w with r := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_dr (w : Data) : w.tapes (sk .divisorRev) = w.dr := rfl
@[simp] theorem Data.update_dr (w : Data) (x : List Bool) :
    Function.update w.tapes (sk .divisorRev) x = ({w with dr := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_old (w : Data) : w.tapes (sk .oldRev) = w.old := rfl
@[simp] theorem Data.update_old (w : Data) (x : List Bool) :
    Function.update w.tapes (sk .oldRev) x = ({w with old := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_trial (w : Data) : w.tapes (sk .trialRev) = w.trial := rfl
@[simp] theorem Data.update_trial (w : Data) (x : List Bool) :
    Function.update w.tapes (sk .trialRev) x = ({w with trial := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_q (w : Data) : w.tapes (sk .quotient) = w.q := rfl
@[simp] theorem Data.update_q (w : Data) (x : List Bool) :
    Function.update w.tapes (sk .quotient) x = ({w with q := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_saved (w : Data) : w.tapes (.inl (.inr .saved)) = w.saved := rfl
@[simp] theorem Data.update_saved (w : Data) (x : List Bool) :
    Function.update w.tapes (.inl (.inr .saved)) x = ({w with saved := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_gtemp (w : Data) : w.tapes (.inl (.inr .temp)) = w.gtemp := rfl
@[simp] theorem Data.update_gtemp (w : Data) (x : List Bool) :
    Function.update w.tapes (.inl (.inr .temp)) x = ({w with gtemp := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_n (w : Data) : w.tapes (ex .num) = w.n := rfl
@[simp] theorem Data.update_n (w : Data) (x : List Bool) :
    Function.update w.tapes (ex .num) x = ({w with n := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_e (w : Data) : w.tapes (ex .den) = w.e := rfl
@[simp] theorem Data.update_e (w : Data) (x : List Bool) :
    Function.update w.tapes (ex .den) x = ({w with e := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_t (w : Data) : w.tapes (ex .temp) = w.t := rfl
@[simp] theorem Data.update_t (w : Data) (x : List Bool) :
    Function.update w.tapes (ex .temp) x = ({w with t := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_g (w : Data) : w.tapes (ex .gcd) = w.g := rfl
@[simp] theorem Data.update_g (w : Data) (x : List Bool) :
    Function.update w.tapes (ex .gcd) x = ({w with g := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

@[simp] theorem Data.lookup_s (w : Data) : w.tapes (ex .stream) = w.s := rfl
@[simp] theorem Data.update_s (w : Data) (x : List Bool) :
    Function.update w.tapes (ex .stream) x = ({w with s := x}).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [Data.tapes, Data.source, Division.tapes]
    | inr k => cases k <;> simp [Data.tapes, Data.source, Gcd.frame]
  | inr k => cases k <;> simp [Data.tapes, Data.frame]

def cfg (label : Option Label) (signs : CarryProtocol.Signs) (w : Data) : Config :=
  ⟨label, CarryProtocol.clean signs, w.tapes⟩
abbrev active (p : Label) (signs : CarryProtocol.Signs) (w : Data) : Config := cfg (some p) signs w
abbrev Runs := CarryProtocol.Runs computer.step

theorem executes (p : Phase) : CarryProtocol.ExecutesAt computer.step (ph p) (outside p) := by
  intro v tapes; rfl


theorem copyN_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .copyN) signs w)
      (active (ph .restoreN) signs {w with n := [], t := w.n.reverse ++ w.t})
      (w.n.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .temp) (ex .num) (by decide)
    computer.step (ph .copyN) (fun _ => ph .restoreN) (executes .copyN) signs w.tapes w.n w.t
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem reverseN_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .reverseN) signs w)
      (active (ph .copyD) signs {w with dr := [], i := w.dr.reverse ++ w.i})
      (w.dr.length + 1) := by
  have h := CarryProtocol.restore_exact (sk .input) (sk .divisorRev) (by decide)
    computer.step (ph .reverseN) (fun _ => ph .copyD) (executes .reverseN) signs w.tapes w.dr w.i
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem copyD_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .copyD) signs w)
      (active (ph .restoreD) signs {w with e := [], t := w.e.reverse ++ w.t})
      (w.e.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .temp) (ex .den) (by decide)
    computer.step (ph .copyD) (fun _ => ph .restoreD) (executes .copyD) signs w.tapes w.e w.t
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem moveG_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .moveG) signs w)
      (active (ph .splitG) signs {w with r := [], t := w.r.reverse ++ w.t})
      (w.r.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .temp) (sk .remainder) (by decide)
    computer.step (ph .moveG) (fun _ => ph .splitG) (executes .moveG) signs w.tapes w.r w.t
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem numerator_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .numerator) signs w)
      (active (dl .start) signs {w with n := [], i := w.n.reverse ++ w.i})
      (w.n.length + 1) := by
  have h := CarryProtocol.restore_exact (sk .input) (ex .num) (by decide)
    computer.step (ph .numerator) (fun _ => dl .start) (executes .numerator) signs w.tapes w.n w.i
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem saveN_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .saveN) signs w)
      (active (ph .restoreQN) signs {w with q := [], t := w.q.reverse ++ w.t})
      (w.q.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .temp) (sk .quotient) (by decide)
    computer.step (ph .saveN) (fun _ => ph .restoreQN) (executes .saveN) signs w.tapes w.q w.t
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem restoreQN_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .restoreQN) signs w)
      (active (ph .moveSavedG) signs {w with t := [], n := w.t.reverse ++ w.n})
      (w.t.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .num) (ex .temp) (by decide)
    computer.step (ph .restoreQN) (fun _ => ph .moveSavedG) (executes .restoreQN) signs w.tapes w.t w.n
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem moveSavedG_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .moveSavedG) signs w)
      (active (ph .restoreG) signs {w with g := [], t := w.g.reverse ++ w.t})
      (w.g.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .temp) (ex .gcd) (by decide)
    computer.step (ph .moveSavedG) (fun _ => ph .restoreG) (executes .moveSavedG) signs w.tapes w.g w.t
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem restoreG_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .restoreG) signs w)
      (active (ph .denominator) signs {w with t := [], d := w.t.reverse ++ w.d})
      (w.t.length + 1) := by
  have h := CarryProtocol.restore_exact (sk .divisor) (ex .temp) (by decide)
    computer.step (ph .restoreG) (fun _ => ph .denominator) (executes .restoreG) signs w.tapes w.t w.d
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem denominator_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .denominator) signs w)
      (active (ph .callD) signs {w with e := [], i := w.e.reverse ++ w.i})
      (w.e.length + 1) := by
  have h := CarryProtocol.restore_exact (sk .input) (ex .den) (by decide)
    computer.step (ph .denominator) (fun _ => ph .callD) (executes .denominator) signs w.tapes w.e w.i
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem saveD_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .saveD) signs w)
      (active (ph .restoreQD) signs {w with q := [], t := w.q.reverse ++ w.t})
      (w.q.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .temp) (sk .quotient) (by decide)
    computer.step (ph .saveD) (fun _ => ph .restoreQD) (executes .saveD) signs w.tapes w.q w.t
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem restoreQD_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .restoreQD) signs w)
      (active (ph .recode) signs {w with t := [], e := w.t.reverse ++ w.e})
      (w.t.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .den) (ex .temp) (by decide)
    computer.step (ph .restoreQD) (fun _ => ph .recode) (executes .restoreQD) signs w.tapes w.t w.e
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem packD_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .packD) signs w)
      (active (ph .delimiter) signs {w with e := [], s := w.e.reverse ++ w.s})
      (w.e.length + 1) := by
  have h := CarryProtocol.restore_exact (ex .stream) (ex .den) (by decide)
    computer.step (ph .packD) (fun _ => ph .delimiter) (executes .packD) signs w.tapes w.e w.s
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

theorem restoreN_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .restoreN) signs w)
      (active (ph .reverseN) signs {w with n := w.t.reverse ++ w.n, dr := w.t.reverse ++ w.dr, t := []}) (w.t.length + 1) := by
  have h := Protocol.split_exact (ex .num) (sk .divisorRev) (ex .temp) (by decide) (by decide) (by decide)
    computer.step (ph .restoreN) (ph .reverseN) (executes .restoreN) signs w.tapes w.t w.n w.dr
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, StackProtocol.tapes3, cfg] using h

theorem restoreD_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .restoreD) signs w)
      (active (.inl (.inr .loop)) signs {w with e := w.t.reverse ++ w.e, d := w.t.reverse ++ w.d, t := []}) (w.t.length + 1) := by
  have h := Protocol.split_exact (ex .den) (sk .divisor) (ex .temp) (by decide) (by decide) (by decide)
    computer.step (ph .restoreD) (.inl (.inr .loop)) (executes .restoreD) signs w.tapes w.t w.e w.d
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, StackProtocol.tapes3, cfg] using h

theorem splitG_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .splitG) signs w)
      (active (ph .numerator) signs {w with g := w.t.reverse ++ w.g, d := w.t.reverse ++ w.d, t := []}) (w.t.length + 1) := by
  have h := Protocol.split_exact (ex .gcd) (sk .divisor) (ex .temp) (by decide) (by decide) (by decide)
    computer.step (ph .splitG) (ph .numerator) (executes .splitG) signs w.tapes w.t w.g w.d
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, StackProtocol.tapes3, cfg] using h


/-- The whole Euclidean subroutine preserves caller bits and all five saved words. -/
theorem gcd_exact (signs : CarryProtocol.Signs) (a b : ℕ) (n e t g s : List Bool) :
    Runs (active (.inl (.inr .loop)) signs
      {i := (encodeNat a).reverse, d := encodeNat b, n := n, e := e, t := t, g := g, s := s})
      (active (ph .moveG) signs {r := encodeNat (Nat.gcd a b), n := n, e := e, t := t, g := g, s := s})
      (Gcd.computeTime (encodeNat a) (encodeNat b)) := by
  let w : Data := {n := n, e := e, t := t, g := g, s := s}
  have h := Call.run (layout w.frame) Sum.inl gcdReturn Gcd.computer.m program
    (fun label => by exact Call.stmt_key_congr (layout (fun _ => [])) (layout w.frame) rfl _ _ _)
    _ _ signs _ (Gcd.compute_encodeNat_exact a b)
  convert h using 1; rfl

/-- The same concrete long-divider is called in quotient-output mode. The saved
sign and caller frame survive both quotient computations. -/
theorem quotient_exact (signs : CarryProtocol.Signs) (a b : ℕ) (n e t g s : List Bool) :
    Runs (active (dl .start) signs
      {i := (encodeNat a).reverse, d := encodeNat b, n := n, e := e, t := t, g := g, s := s})
      (active (quotientReturn signs) signs {q := encodeNat (a / b), n := n, e := e, t := t, g := g, s := s})
      (Division.computeTime false (encodeNat a).reverse (encodeNat b)) := by
  have hd := Division.compute_encodeNat_exact false a b
  simp only [Division.Runs, FinTM2.step, Division.computer] at hd
  have hf := MachineFrame.run_program (Division.program false) (J := Gcd.FrameStack)
    (R := Empty) (τ := Unit) Empty.elim
      (Division.cfg (some .start) false (encodeNat a).reverse (encodeNat b) [] [] [] [] [])
      () (Gcd.frame [] []) (Division.computeTime false (encodeNat a).reverse (encodeNat b))
  rw [hd] at hf
  let w : Data := {n := n, e := e, t := t, g := g, s := s}
  have h := Call.run (layout w.frame) ql quotientReturn quotientProgram program
    (fun label => by exact Call.stmt_key_congr (layout (fun _ => [])) (layout w.frame) rfl _ _ _)
    _ _ signs _ hf
  convert h using 1; rfl


@[simp] theorem step_first_cons (signs : CarryProtocol.Signs) (w : Data) (b : Bool) (rest : List Bool) :
    computer.step (active (ph .first) signs {w with s := true :: b :: rest}) =
      some (active (ph .first) signs {w with s := rest, n := b :: w.n}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

@[simp] theorem step_delimiter (signs : CarryProtocol.Signs) (w : Data) (rest : List Bool) :
    computer.step (active (ph .first) signs {w with s := false :: rest}) =
      some (active (ph .second) signs {w with s := rest}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

@[simp] theorem step_second_cons (signs : CarryProtocol.Signs) (w : Data) (b : Bool) (rest : List Bool) :
    computer.step (active (ph .second) signs {w with s := b :: rest}) =
      some (active (ph .second) signs {w with s := rest, e := b :: w.e}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

@[simp] theorem step_second_nil (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .second) signs {w with s := []}) =
      some (active (ph .sign) signs {w with s := []}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem first_exact (signs : CarryProtocol.Signs) (w : Data) (word rest : List Bool) :
    Runs (active (ph .first) signs {w with s := Holant.Algebraic.frame word ++ rest})
      (active (ph .second) signs {w with s := rest, n := word.reverse ++ w.n}) (word.length + 1) := by
  induction word generalizing w with
  | nil => simpa [Runs, FinTM2.step, Holant.Algebraic.frame] using CarryProtocol.Runs.one (step_delimiter signs w rest)
  | cons bit word ih =>
    have h := (CarryProtocol.Runs.one (step_first_cons signs w bit (Holant.Algebraic.frame word ++ rest))).trans
      (ih {w with n := bit :: w.n})
    simpa [Runs, FinTM2.step, Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using h

theorem second_exact (signs : CarryProtocol.Signs) (w : Data) (word : List Bool) :
    Runs (active (ph .second) signs {w with s := word})
      (active (ph .sign) signs {w with s := [], e := word.reverse ++ w.e}) (word.length + 1) := by
  induction word generalizing w with
  | nil => simpa [Runs, FinTM2.step] using CarryProtocol.Runs.one (step_second_nil signs w)
  | cons bit word ih =>
    have h := (CarryProtocol.Runs.one (step_second_cons signs w bit word)).trans (ih {w with e := bit :: w.e})
    simpa [Runs, FinTM2.step, List.reverse_cons, List.append_assoc] using h

theorem step_sign (n : ℤ) (w : Data) :
    computer.step (active (ph .sign) (false, false) {w with n := encoding.encode n}) =
      some (active (ph (if negative n then .inc else .start)) (negative n, false)
        {w with n := encodeNat (payload n)}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux,
    encoding_head, encoding_tail, CarryProtocol.clean]
  congr 2

theorem increment_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .inc) signs {w with t := []})
      (active (ph .start) signs {w with n := increment w.n, t := []}) (2 * (carryCount w.n + 1)) := by
  have h := CarryProtocol.increment_exact_frame (ex .num) (ex .temp) (by decide)
    computer.step (ph .inc) (ph .restoreInc) (fun _ => ph .start)
    (executes .inc) (executes .restoreInc) signs w.tapes w.n
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

def parseTime (n : ℤ) (d : ℕ) : ℕ :=
  (encoding.encode n).length + (encodeNat d).length + 3 +
    if negative n then 2 * (carryCount (encodeNat (payload n)) + 1) else 0

theorem parse_exact (n : ℤ) (d : ℕ) :
    Runs (active (ph .first) (false, false) {s := fractionEncoding.encode (n, d)})
      (active (ph .start) (negative n, false) {n := encodeNat n.natAbs, e := encodeNat d}) (parseTime n d) := by
  have h₁ := first_exact (false, false) ({} : Data) (encoding.encode n).reverse (encodeNat d).reverse
  have h₂ := second_exact (false, false) ({n := encoding.encode n} : Data) (encodeNat d).reverse
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₁ h₂
  have h₃ := CarryProtocol.Runs.one (step_sign n {e := encodeNat d})
  have h := (h₁.trans h₂).trans h₃
  cases hn : negative n
  · simp only [fractionEncoding, parseTime, hn, Bool.false_eq_true, ↓reduceIte,
      ← payload_magnitude n, Bool.toNat_false, Nat.add_zero] at h ⊢
    convert h using 1; omega
  · have h₄ := increment_exact (true, false) {n := encodeNat (payload n), e := encodeNat d}
    simp only [hn, ↓reduceIte] at h
    have ht := h.trans h₄
    simp only [fractionEncoding, parseTime, hn, ↓reduceIte, increment_encodeNat,
      ← payload_magnitude n, Bool.toNat_true] at ht ⊢
    convert ht using 1; omega


@[simp] theorem step_start_nil (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .start) signs {w with e := []}) =
      some (active (ph .zeroClear) signs {w with e := []}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

@[simp] theorem step_start_cons (signs : CarryProtocol.Signs) (w : Data) (b : Bool) (rest : List Bool) :
    computer.step (active (ph .start) signs {w with e := b :: rest}) =
      some (active (ph .copyN) signs {w with e := b :: rest}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem zeroClear_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .zeroClear) signs w)
      (active (ph .zeroDen) signs {w with n := []}) (w.n.length + 1) := by
  have h := NormalizeProtocol.clear_exact (ex .temp) (ex .num)
    computer.step (ph .zeroClear) (fun _ => ph .zeroDen) (executes .zeroClear) signs w.tapes w.n w.t
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

@[simp] theorem step_zeroDen (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .zeroDen) signs w) =
      some (active (ph .packD) signs {w with e := true :: w.e}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.clearBit, CarryProtocol.clean]
  congr 2

@[simp] theorem step_callD (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .callD) signs w) =
      some (active (dl .start) (signs.1, true) w) := rfl

@[simp] theorem step_recode_nil (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .recode) signs {w with n := []}) =
      some (active (ph .packD) signs {w with n := []}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

@[simp] theorem step_recode_cons (sign stage bit : Bool) (w : Data) (rest : List Bool) :
    computer.step (active (ph .recode) (sign, stage) {w with n := bit :: rest}) =
      some (if sign then active (ph .dec) (sign, stage) {w with n := bit :: rest}
        else active (ph .packD) (sign, stage) {w with n := false :: bit :: rest}) := by
  cases sign <;>
    simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
      CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
      BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial] <;> congr 2

@[simp] theorem step_tag (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .tag) signs w) =
      some (active (ph .packD) signs {w with n := true :: w.n}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.clearBit, CarryProtocol.clean]
  congr 2

theorem decrement_exact (signs : CarryProtocol.Signs) (w : Data) :
    Runs (active (ph .dec) signs {w with t := []})
      (active (ph .tag) signs {w with n := decrement w.n, t := []}) (2 * (borrowCount w.n + 1)) := by
  have h := CarryProtocol.decrement_exact_frame (ex .num) (ex .temp) (by decide)
    computer.step (ph .dec) (ph .restoreDec) (fun _ => ph .tag)
    (executes .dec) (executes .restoreDec) signs w.tapes w.n
  cases w
  simpa [Runs, FinTM2.step, CarryProtocol.cfg, CarryProtocol.tapes2, cfg] using h

def recodeTime (sign : Bool) (word : List Bool) : ℕ :=
  if word = [] then 1 else if sign then 2 * (borrowCount word + 1) + 2 else 1

theorem recode_exact (signs : CarryProtocol.Signs) (n d : List Bool) :
    Runs (active (ph .recode) signs {n := n, e := d})
      (active (ph .packD) signs {n := recode signs.1 n, e := d}) (recodeTime signs.1 n) := by
  rcases signs with ⟨sign, stage⟩
  cases n with
  | nil => simpa [Runs, FinTM2.step, recodeTime, recode] using
      CarryProtocol.Runs.one (step_recode_nil (sign, stage) {e := d})
  | cons bit rest =>
    cases sign
    · simpa [Runs, FinTM2.step, recodeTime, recode] using
        CarryProtocol.Runs.one (step_recode_cons false stage bit {e := d} rest)
    · have h₁ := CarryProtocol.Runs.one (step_recode_cons true stage bit {e := d} rest)
      simp only [↓reduceIte] at h₁
      have h₂ := decrement_exact (true, stage) {n := bit :: rest, e := d}
      have h₃ := CarryProtocol.Runs.one (step_tag (true, stage) {n := decrement (bit :: rest), e := d})
      have h := (h₁.trans h₂).trans h₃
      simp only [recodeTime, List.cons_ne_nil, ↓reduceIte, recode] at h ⊢
      convert h using 1; omega

@[simp] theorem step_packDelimiter (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .delimiter) signs w) =
      some (active (ph .packN) signs {w with s := false :: w.s}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.clearBit, CarryProtocol.clean]
  congr 2

@[simp] theorem step_packN_cons (signs : CarryProtocol.Signs) (w : Data) (bit : Bool) (rest : List Bool) :
    computer.step (active (ph .packN) signs {w with n := bit :: rest}) =
      some (active (ph .packN) signs {w with n := rest, s := true :: bit :: w.s}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux, again,
    CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

@[simp] theorem step_packN_nil (signs : CarryProtocol.Signs) (w : Data) :
    computer.step (active (ph .packN) signs {w with n := []}) =
      some (cfg none (false, false) {w with n := []}) := by
  simp [FinTM2.step, TM2.step, program, outside, cfg, TM2.stepAux,
    CarryProtocol.saveBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem packN_exact (signs : CarryProtocol.Signs) (w : Data) (word acc rest : List Bool) :
    Runs (active (ph .packN) signs {w with n := word, s := Holant.Algebraic.frame acc ++ rest})
      (cfg none (false, false) {w with n := [], s := Holant.Algebraic.frame (word.reverse ++ acc) ++ rest})
      (word.length + 1) := by
  induction word generalizing acc with
  | nil => simpa [Runs, FinTM2.step] using
      CarryProtocol.Runs.one (step_packN_nil signs {w with s := Holant.Algebraic.frame acc ++ rest})
  | cons bit word ih =>
    have h₁ := CarryProtocol.Runs.one (step_packN_cons signs {w with s := Holant.Algebraic.frame acc ++ rest} bit word)
    have h := h₁.trans (ih (bit :: acc))
    simpa [Runs, FinTM2.step, Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using h

/-- Both prepared component words are serialized by counted bit pushes; every
scratch stack and the finite state are clean at halt. -/
theorem pack_exact (signs : CarryProtocol.Signs) (n d : List Bool) :
    Runs (active (ph .packD) signs {n := n, e := d})
      (cfg none (false, false) {s := Holant.Algebraic.frame n.reverse ++ d.reverse})
      (n.length + d.length + 3) := by
  have h₁ := packD_exact signs {n := n, e := d}
  simp only [List.append_nil] at h₁
  have h₂ := CarryProtocol.Runs.one (step_packDelimiter signs {n := n, s := d.reverse})
  have h₃ := packN_exact signs ({} : Data) n [] d.reverse
  simp only [List.append_nil, Holant.Algebraic.frame, List.cons_append, List.nil_append] at h₃
  have h := (h₁.trans h₂).trans h₃
  convert h using 1; omega


/-- Preserve both operands and arrange exactly the gcd engine's input order. -/
theorem prepare_exact (signs : CarryProtocol.Signs) (n d : List Bool) :
    Runs (active (ph .copyN) signs {n := n, e := d})
      (active (.inl (.inr .loop)) signs {i := n.reverse, d := d, n := n, e := d})
      (3 * n.length + 2 * d.length + 5) := by
  have h₁ := copyN_exact signs {n := n, e := d}
  have h₂ := restoreN_exact signs {t := n.reverse, e := d}
  have h₃ := reverseN_exact signs {n := n, dr := n, e := d}
  have h₄ := copyD_exact signs {i := n.reverse, n := n, e := d}
  have h₅ := restoreD_exact signs {i := n.reverse, n := n, t := d.reverse}
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h₁ h₂ h₃ h₄ h₅
  have h := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  convert h using 1; omega

def quotientTime (n d : ℕ) : ℕ :=
  Division.computeTime false (encodeNat n).reverse (encodeNat (Nat.gcd n d)) +
  Division.computeTime false (encodeNat d).reverse (encodeNat (Nat.gcd n d)) +
  4 * (encodeNat (Nat.gcd n d)).length + (encodeNat n).length + (encodeNat d).length +
  2 * (encodeNat (n / Nat.gcd n d)).length + 2 * (encodeNat (d / Nat.gcd n d)).length + 11

/-- Both gcd divisions, operand copying, and the call-stage flag are counted. -/
theorem quotients_exact (sign : Bool) (n d : ℕ) :
    Runs (active (ph .moveG) (sign, false)
      {r := encodeNat (Nat.gcd n d), n := encodeNat n, e := encodeNat d})
      (active (ph .recode) (sign, true)
        {n := encodeNat (n / Nat.gcd n d), e := encodeNat (d / Nat.gcd n d)})
      (quotientTime n d) := by
  let g := Nat.gcd n d
  let a := n / g
  let b := d / g
  have h₁ := moveG_exact (sign, false) {r := encodeNat g, n := encodeNat n, e := encodeNat d}
  have h₂ := splitG_exact (sign, false) {t := (encodeNat g).reverse, n := encodeNat n, e := encodeNat d}
  have h₃ := numerator_exact (sign, false) {d := encodeNat g, g := encodeNat g, n := encodeNat n, e := encodeNat d}
  have h₄ := quotient_exact (sign, false) n g [] (encodeNat d) [] (encodeNat g) []
  have h₅ := saveN_exact (sign, false) {q := encodeNat a, e := encodeNat d, g := encodeNat g}
  have h₆ := restoreQN_exact (sign, false) {t := (encodeNat a).reverse, e := encodeNat d, g := encodeNat g}
  have h₇ := moveSavedG_exact (sign, false) {n := encodeNat a, e := encodeNat d, g := encodeNat g}
  have h₈ := restoreG_exact (sign, false) {n := encodeNat a, e := encodeNat d, t := (encodeNat g).reverse}
  have h₉ := denominator_exact (sign, false) {n := encodeNat a, e := encodeNat d, d := encodeNat g}
  have h₁₀ := CarryProtocol.Runs.one (step_callD (sign, false)
    {n := encodeNat a, i := (encodeNat d).reverse, d := encodeNat g})
  have h₁₁ := quotient_exact (sign, true) d g (encodeNat a) [] [] [] []
  have h₁₂ := saveD_exact (sign, true) {n := encodeNat a, q := encodeNat b}
  have h₁₃ := restoreQD_exact (sign, true) {n := encodeNat a, t := (encodeNat b).reverse}
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse,
    quotientReturn, Bool.false_eq_true, ↓reduceIte] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₁ h₁₂ h₁₃
  have h := (((((((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).trans h₉).trans h₁₀).trans h₁₁).trans h₁₂).trans h₁₃
  unfold quotientTime
  dsimp only [a, b, g] at h
  convert h using 1; omega

def normalizeTime (sign : Bool) (n d : ℕ) : ℕ :=
  if d = 0 then (encodeNat n).length + 7 else
    1 + (3 * (encodeNat n).length + 2 * (encodeNat d).length + 5) +
      Gcd.computeTime (encodeNat n) (encodeNat d) + quotientTime n d +
      recodeTime sign (encodeNat (n / Nat.gcd n d)) +
      (recode sign (encodeNat (n / Nat.gcd n d))).length +
      (encodeNat (d / Nat.gcd n d)).length + 3

/-- Complete normalization from prepared sign/magnitude and denominator, with a
literal clean framed pair result and exact operational time. -/
theorem normalize_exact (sign : Bool) (n d : ℕ) :
    Runs (active (ph .start) (sign, false) {n := encodeNat n, e := encodeNat d})
      (cfg none (false, false)
        {s := Holant.Algebraic.frame (normalizeBits sign (encodeNat n) (encodeNat d)).1.reverse ++
          (normalizeBits sign (encodeNat n) (encodeNat d)).2.reverse})
      (normalizeTime sign n d) := by
  by_cases hd : d = 0
  · subst d
    have h₁ := CarryProtocol.Runs.one (step_start_nil (sign, false) {n := encodeNat n})
    have h₂ := zeroClear_exact (sign, false) {n := encodeNat n}
    have h₃ := CarryProtocol.Runs.one (step_zeroDen (sign, false) ({} : Data))
    have h₄ := pack_exact (sign, false) [] [true]
    have h := ((h₁.trans h₂).trans h₃).trans h₄
    simp only [normalizeBits, ↓reduceIte, normalizeTime, List.length_nil, List.length_cons] at h ⊢
    convert h using 1 <;> first | rfl | omega
  · have h₁ : Runs (active (ph .start) (sign, false) {n := encodeNat n, e := encodeNat d})
        (active (ph .copyN) (sign, false) {n := encodeNat n, e := encodeNat d}) 1 := by
      cases hbits : encodeNat d with
      | nil => exact False.elim (hd ((encodeNat_eq_nil d).mp hbits))
      | cons bit rest => exact CarryProtocol.Runs.one (step_start_cons (sign, false) {n := encodeNat n} bit rest)
    have h₂ := prepare_exact (sign, false) (encodeNat n) (encodeNat d)
    have h₃ := gcd_exact (sign, false) n d (encodeNat n) (encodeNat d) [] [] []
    have h₄ := quotients_exact sign n d
    have h₅ := recode_exact (sign, true) (encodeNat (n / Nat.gcd n d)) (encodeNat (d / Nat.gcd n d))
    have h₆ := pack_exact (sign, true) (recode sign (encodeNat (n / Nat.gcd n d))) (encodeNat (d / Nat.gcd n d))
    have h := ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆
    simp only [normalizeTime, hd, ↓reduceIte, normalizeBits, encodeNat_eq_nil,
      GcdBits.gcdBits_encodeNat, DivisionBits.divideBits_encodeNat] at h ⊢
    convert h using 1; omega


@[simp] theorem cfg_init (word : List Bool) :
    active (ph .first) (false, false) {s := word} = initList computer word := by
  dsimp [active, cfg, initList, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

@[simp] theorem cfg_halt (word : List Bool) :
    cfg none (false, false) {s := word} = haltList computer word := by
  dsimp [cfg, haltList, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

def time (n : ℤ) (d : ℕ) : ℕ := parseTime n d + normalizeTime (negative n) n.natAbs d

/-- The output framing uses the literal numerator's intEquivNat code. -/
theorem encoded_exact (n : ℤ) (d : ℕ) :
    Runs (initList computer (fractionEncoding.encode (n, d)))
      (haltList computer (EncodedAddition.inputEncoding.encode
        (Equiv.intEquivNat (mkRat n d).num, (mkRat n d).den))) (time n d) := by
  have h := (parse_exact n d).trans (normalize_exact (negative n) n.natAbs d)
  rw [normalizeBits_integer, cfg_halt, cfg_init] at h
  simpa [Runs, FinTM2.step, time, Nat.add_comm, EncodedAddition.inputEncoding, encoding] using h

theorem recode_length_le (sign : Bool) (word : List Bool) :
    (recode sign word).length ≤ word.length + 1 := by
  have h := decrement_length_le word
  cases word <;> cases sign <;> simp_all [recode]

theorem recodeTime_le (sign : Bool) (word : List Bool) :
    recodeTime sign word ≤ 2 * word.length + 4 := by
  have h := borrowCount_le word
  unfold recodeTime
  split_ifs <;> omega

theorem quotient_length_le (a b : ℕ) :
    (encodeNat (a / b)).length ≤ (encodeNat a).length := by
  simpa only [DivisionBits.divideBits_encodeNat, List.length_reverse] using
    DivisionBits.divideBits_quotient_length_le (encodeNat a).reverse (encodeNat b)

theorem gcd_length_le (a b : ℕ) :
    (encodeNat (Nat.gcd a b)).length ≤ (encodeNat a).length + (encodeNat b).length := by
  have h := GcdBits.loop_length_sum_le (GcdBits.fuel (encodeNat a) (encodeNat b))
    (encodeNat a) (encodeNat b) (canonical_encodeNat a) (canonical_encodeNat b)
  simpa only [GcdBits.loop_fuel_encodeNat, List.length_nil, Nat.add_zero] using h

theorem quotientTime_le (n d : ℕ) :
    quotientTime n d ≤ 12 * ((encodeNat n).length + (encodeNat d).length) ^ 2 +
      25 * ((encodeNat n).length + (encodeNat d).length) + 19 := by
  have hn := Division.computeTime_le false (encodeNat n).reverse (encodeNat (Nat.gcd n d))
  have hd := Division.computeTime_le false (encodeNat d).reverse (encodeNat (Nat.gcd n d))
  simp only [List.length_reverse] at hn hd
  have hg := gcd_length_le n d
  have hqn := quotient_length_le n (Nat.gcd n d)
  have hqd := quotient_length_le d (Nat.gcd n d)
  let s := (encodeNat n).length + (encodeNat d).length
  have pn : (3 * ((encodeNat n).length + (encodeNat (Nat.gcd n d)).length) + 7) * (encodeNat n).length ≤
      (6 * s + 7) * s := Nat.mul_le_mul (by dsimp [s]; omega) (by dsimp [s]; omega)
  have pd : (3 * ((encodeNat d).length + (encodeNat (Nat.gcd n d)).length) + 7) * (encodeNat d).length ≤
      (6 * s + 7) * s := Nat.mul_le_mul (by dsimp [s]; omega) (by dsimp [s]; omega)
  unfold quotientTime
  dsimp [s] at pn pd
  nlinarith

theorem normalizeTime_le (sign : Bool) (n d : ℕ) :
    normalizeTime sign n d ≤ 128 * ((encodeNat n).length + (encodeNat d).length + 1) ^ 3 := by
  have hg := Gcd.computeTime_le (encodeNat n) (encodeNat d) (canonical_encodeNat n) (canonical_encodeNat d)
  have hq := quotientTime_le n d
  have hr := recodeTime_le sign (encodeNat (n / Nat.gcd n d))
  have hl := recode_length_le sign (encodeNat (n / Nat.gcd n d))
  have hqn := quotient_length_le n (Nat.gcd n d)
  have hqd := quotient_length_le d (Nat.gcd n d)
  unfold normalizeTime
  split <;> nlinarith

theorem parseTime_le (n : ℤ) (d : ℕ) :
    parseTime n d ≤ 3 * (encoding.encode n).length + (encodeNat d).length + 5 := by
  have hc := carryCount_le (encodeNat (payload n))
  have ht : (encodeNat (payload n)).length ≤ (encoding.encode n).length := by
    rw [← encoding_tail]; simp
  unfold parseTime
  split_ifs <;> omega

/-- Input size is the actual serialized bit length, including integer parity and
framing. The polynomial counts every helper and cleanup transition. -/
theorem time_le (n : ℤ) (d : ℕ) :
    time n d ≤ 200 * ((fractionEncoding.encode (n,d)).length + 1) ^ 3 := by
  have hp := parseTime_le n d
  have hn := normalizeTime_le (negative n) n.natAbs d
  have hm := magnitudeBits_length_le n
  have hs : (encodeNat n.natAbs).length + (encodeNat d).length + 1 ≤
      (fractionEncoding.encode (n,d)).length + 1 := by simp only [fractionEncoding_length]; omega
  have hc := Nat.pow_le_pow_left hs 3
  have hnx := hn.trans (Nat.mul_le_mul_left 128 hc)
  have hpx : parseTime n d ≤ 3 * (fractionEncoding.encode (n,d)).length + 5 := by
    simp only [fractionEncoding_length]; omega
  calc
    time n d ≤ (3 * (fractionEncoding.encode (n,d)).length + 5) +
        128 * ((fractionEncoding.encode (n,d)).length + 1) ^ 3 := Nat.add_le_add hpx hnx
    _ ≤ _ := by ring_nf; omega


abbrev machine : Machine where
  K := K
  input := computer.k₀
  output := computer.k₁
  Label := Label
  main := computer.main
  State := Memory
  initial := computer.initialState
  program := program

/-- Real clean Boolean-machine witness for the canonical component pair. -/
noncomputable def computes : Computes fractionEncoding EncodedAddition.inputEncoding
    (fun p : ℤ × ℕ => (Equiv.intEquivNat (mkRat p.1 p.2).num, (mkRat p.1 p.2).den)) where
  machine := machine
  time := 200 * (Polynomial.X + 1) ^ 3
  outputs p := by
    refine { steps := time p.1 p.2, evals_in_steps := encoded_exact p.1 p.2, steps_le_m := ?_ }
    simpa using time_le p.1 p.2

theorem outside_budget (p : Phase) : TM2Cost.budget (outside p) ≤ 8 := by
  cases p <;> decide

theorem program_budget (p : Label) : TM2Cost.budget (program p) ≤ 12 := by
  cases p with
  | inl p => simpa only [program, Call.budget_stmt] using Gcd.program_budget p
  | inr p => cases p with
    | inl p => cases p with
      | inl p => simpa only [program, quotientProgram, MachineFrame.program,
          Call.budget_stmt, MachineFrame.budget_stmt] using Division.program_budget false p
      | inr p => exact p.elim
    | inr p => exact (outside_budget p).trans (by decide)

@[simp] theorem stack_count : Fintype.card computer.K = 14 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 58 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 72 := by decide

end Holant.Complexity.RationalArithmetic.Normalization
