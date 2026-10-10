import Holant.Complexity.BinaryArithmetic.Division
import Holant.Complexity.BinaryArithmetic.GcdBits
import Holant.Complexity.MachineReturn

/-!
# A finite Euclidean gcd machine

Each Euclidean iteration calls the actual binary remainder machine. Explicit
stack loops save its divisor, then rotate divisor and remainder into the next
operand pair. The saved frame survives the structurally compiled call exactly.
No numeric arithmetic is performed by a control-register callback.
-/

namespace Holant.Complexity.BinaryArithmetic.Gcd

open Turing Computability
open Turing.TM2.Stmt

inductive FrameStack
  | saved | temp
  deriving DecidableEq
instance : Fintype FrameStack := ⟨{.saved, .temp}, by intro k; cases k <;> simp⟩

inductive OuterLabel
  | loop | copyB | restoreB | rotateA | rotateR | restoreR | finish
  deriving DecidableEq
instance : Fintype OuterLabel :=
  ⟨{.loop, .copyB, .restoreB, .rotateA, .rotateR, .restoreR, .finish}, by intro k; cases k <;> simp⟩

abbrev Stack := Division.Stack ⊕ FrameStack
abbrev Label := Division.Label ⊕ OuterLabel
abbrev Memory := Division.State × Unit
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Memory

def initial : Memory := (Division.initial, ())
def saveBit (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), v.2)
def again (label : OuterLabel) : Statement := load (fun _ => initial) (goto (fun _ => .inr label))
def returnLabel (_ : Unit) : OuterLabel := .rotateA

/-- Euclidean control and data movement use only single-bit stack primitives. -/
def outside : OuterLabel → Statement
  | .loop => peek (.inl .divisor) saveBit
      (branch (fun v => v.1.2.1.isSome) (again .copyB) (again .finish))
  | .copyB => pop (.inl .divisor) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inr .temp) (fun v => v.1.2.1.getD false) (again .copyB))
        (again .restoreB))
  | .restoreB => pop (.inr .temp) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .divisor) (fun v => v.1.2.1.getD false)
          (push (.inr .saved) (fun v => v.1.2.1.getD false) (again .restoreB)))
        (load (fun _ => initial) (goto (fun _ => .inl .start))))
  | .rotateA => pop (.inr .saved) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .input) (fun v => v.1.2.1.getD false) (again .rotateA))
        (again .rotateR))
  | .rotateR => pop (.inl .remainder) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inr .temp) (fun v => v.1.2.1.getD false) (again .rotateR))
        (again .restoreR))
  | .restoreR => pop (.inr .temp) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .divisor) (fun v => v.1.2.1.getD false) (again .restoreR))
        (again .loop))
  | .finish => pop (.inl .input) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .remainder) (fun v => v.1.2.1.getD false) (again .finish))
        (load (fun _ => initial) halt))

abbrev computer : FinTM2 where
  K := Stack
  k₀ := .inl .input
  k₁ := .inl .remainder
  Γ _ := Bool
  Λ := Label
  main := .inr .loop
  σ := Memory
  initialState := initial
  m := MachineReturn.program returnLabel (Division.program true) outside

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def frame (saved temp : List Bool) : FrameStack → List Bool
  | .saved => saved
  | .temp => temp

def cfg (label : Option OuterLabel) (i d r saved temp : List Bool) : Config :=
  ⟨label.map Sum.inr, initial, Sum.elim (Division.tapes i d r [] [] [] []) (frame saved temp)⟩

def dividerCfg (c : Division.Config) (saved temp : List Bool) : Config :=
  MachineReturn.cfg returnLabel c () (frame saved temp)

@[simp] theorem update_saved (source : Division.Stack → List Bool) (saved temp word : List Bool) :
    Function.update (Sum.elim source (frame saved temp)) (.inr .saved) word =
      Sum.elim source (frame word temp) := by
  funext k
  cases k with
  | inl k => simp
  | inr k => cases k <;> simp [frame]

@[simp] theorem update_temp (source : Division.Stack → List Bool) (saved temp word : List Bool) :
    Function.update (Sum.elim source (frame saved temp)) (.inr .temp) word =
      Sum.elim source (frame saved word) := by
  funext k
  cases k with
  | inl k => simp
  | inr k => cases k <;> simp [frame]

def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

/-- The compiled remainder call preserves both saved words and its exact runtime. -/
theorem lift_division {a b : Division.Config} {time : ℕ}
    (h : Division.Runs true a b time) (saved temp : List Bool) :
    Runs (dividerCfg a saved temp) (dividerCfg b saved temp) time := by
  exact MachineReturn.run_program returnLabel (Division.program true) outside
    a () (frame saved temp) time b h

@[simp] theorem step_loop_nil (i : List Bool) :
    computer.step (cfg (some .loop) i [] [] [] []) = some (cfg (some .finish) i [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_loop_cons (bit : Bool) (i d : List Bool) :
    computer.step (cfg (some .loop) i (bit :: d) [] [] []) = some (cfg (some .copyB) i (bit :: d) [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_copy_cons (bit : Bool) (i d r saved temp : List Bool) :
    computer.step (cfg (some .copyB) i (bit :: d) r saved temp) = some (cfg (some .copyB) i d r saved (bit :: temp)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_copy_nil (i r saved temp : List Bool) :
    computer.step (cfg (some .copyB) i [] r saved temp) = some (cfg (some .restoreB) i [] r saved temp) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_cons (bit : Bool) (i d r saved temp : List Bool) :
    computer.step (cfg (some .restoreB) i d r saved (bit :: temp)) = some (cfg (some .restoreB) i (bit :: d) r (bit :: saved) temp) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_rotateA_cons (bit : Bool) (i d r saved temp : List Bool) :
    computer.step (cfg (some .rotateA) i d r (bit :: saved) temp) = some (cfg (some .rotateA) (bit :: i) d r saved temp) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_rotateA_nil (i d r temp : List Bool) :
    computer.step (cfg (some .rotateA) i d r [] temp) = some (cfg (some .rotateR) i d r [] temp) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_rotateR_cons (bit : Bool) (i d r temp : List Bool) :
    computer.step (cfg (some .rotateR) i d (bit :: r) [] temp) = some (cfg (some .rotateR) i d r [] (bit :: temp)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_rotateR_nil (i d temp : List Bool) :
    computer.step (cfg (some .rotateR) i d [] [] temp) = some (cfg (some .restoreR) i d [] [] temp) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restoreR_cons (bit : Bool) (i d temp : List Bool) :
    computer.step (cfg (some .restoreR) i d [] [] (bit :: temp)) = some (cfg (some .restoreR) i (bit :: d) [] [] temp) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restoreR_nil (i d : List Bool) :
    computer.step (cfg (some .restoreR) i d [] [] []) = some (cfg (some .loop) i d [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    frame, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_finish_cons (bit : Bool) (i r : List Bool) :
    computer.step (cfg (some .finish) (bit :: i) [] r [] []) = some (cfg (some .finish) i [] (bit :: r) [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_finish_nil (r : List Bool) :
    computer.step (cfg (some .finish) [] [] r [] []) = some (cfg none [] [] r [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, again, Division.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_nil (i d r saved : List Bool) :
    computer.step (cfg (some .restoreB) i d r saved []) =
      some (dividerCfg (Division.cfg (some .start) false i d r [] [] [] []) saved []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, cfg, outside,
    TM2.stepAux, saveBit, initial, Division.initial, dividerCfg, MachineReturn.cfg,
    Division.cfg, Division.reset, MachineFrame.update_left, frame,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem dividerCfg_final (r saved temp : List Bool) :
    dividerCfg (Division.finalCfg true r) saved temp = cfg (some .rotateA) [] [] r saved temp := rfl

/-- Pop the divisor into a temporary reverse word. -/
theorem copy_exact (i d r saved temp : List Bool) :
    Runs (cfg (some .copyB) i d r saved temp)
      (cfg (some .restoreB) i [] r saved (d.reverse ++ temp)) (d.length + 1) := by
  induction d generalizing temp with
  | nil => simpa using Runs.one (step_copy_nil i r saved temp)
  | cons bit d ih =>
    have h := (Runs.one (step_copy_cons bit i d r saved temp)).trans (ih (bit :: temp))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Restore the divisor and create its preserved copy before the remainder call. -/
theorem restore_exact (i d r saved temp : List Bool) :
    Runs (cfg (some .restoreB) i d r saved temp)
      (dividerCfg (Division.cfg (some .start) false i (temp.reverse ++ d) r [] [] [] [])
        (temp.reverse ++ saved) []) (temp.length + 1) := by
  induction temp generalizing d saved with
  | nil => simpa using Runs.one (step_restore_nil i d r saved)
  | cons bit temp ih =>
    have h := (Runs.one (step_restore_cons bit i d r saved temp)).trans (ih (bit :: d) (bit :: saved))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Saved divisor becomes the next MSB-first dividend by an explicit reversal. -/
theorem rotateA_exact (i d r saved temp : List Bool) :
    Runs (cfg (some .rotateA) i d r saved temp)
      (cfg (some .rotateR) (saved.reverse ++ i) d r [] temp) (saved.length + 1) := by
  induction saved generalizing i with
  | nil => simpa using Runs.one (step_rotateA_nil i d r temp)
  | cons bit saved ih =>
    have h := (Runs.one (step_rotateA_cons bit i d r saved temp)).trans (ih (bit :: i))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Move the computed remainder through a temporary reverse word. -/
theorem rotateR_exact (i d r temp : List Bool) :
    Runs (cfg (some .rotateR) i d r [] temp)
      (cfg (some .restoreR) i d [] [] (r.reverse ++ temp)) (r.length + 1) := by
  induction r generalizing temp with
  | nil => simpa using Runs.one (step_rotateR_nil i d temp)
  | cons bit r ih =>
    have h := (Runs.one (step_rotateR_cons bit i d r temp)).trans (ih (bit :: temp))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Restore the remainder as the next little-endian divisor. -/
theorem restoreR_exact (i d temp : List Bool) :
    Runs (cfg (some .restoreR) i d [] [] temp)
      (cfg (some .loop) i (temp.reverse ++ d) [] [] []) (temp.length + 1) := by
  induction temp generalizing d with
  | nil => simpa using Runs.one (step_restoreR_nil i d)
  | cons bit temp ih =>
    have h := (Runs.one (step_restoreR_cons bit i d temp)).trans (ih (bit :: d))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Convert the last dividend to canonical output order and halt cleanly. -/
theorem finish_exact (i r : List Bool) :
    Runs (cfg (some .finish) i [] r [] [])
      (cfg none [] [] (i.reverse ++ r) [] []) (i.length + 1) := by
  induction i generalizing r with
  | nil => simpa using Runs.one (step_finish_nil r)
  | cons bit i ih =>
    have h := (Runs.one (step_finish_cons bit i r)).trans (ih (bit :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Checking the zero divisor and finalizing the canonical gcd costs linearly. -/
theorem done_exact (a : List Bool) :
    Runs (cfg (some .loop) a.reverse [] [] [] []) (cfg none [] [] a [] []) (a.length + 2) := by
  have h := (Runs.one (step_loop_nil a.reverse)).trans (finish_exact a.reverse [])
  simpa [Nat.add_assoc] using h

/-- Every copy, remainder-call and operand-rotation transition in one Euclidean step. -/
def cycleTime (a b : List Bool) : ℕ :=
  Division.computeTime true a.reverse b + 3 * b.length + 2 * (GcdBits.remainder a b).length + 6

theorem cycle_exact (a b : List Bool) (ha : Canonical a) (hb : b ≠ []) :
    Runs (cfg (some .loop) a.reverse b [] [] [])
      (cfg (some .loop) b.reverse (GcdBits.remainder a b) [] [] []) (cycleTime a b) := by
  have h₁ : Runs (cfg (some .loop) a.reverse b [] [] [])
      (cfg (some .copyB) a.reverse b [] [] []) 1 := by
    cases b with
    | nil => contradiction
    | cons bit b => exact Runs.one (step_loop_cons bit a.reverse b)
  have h₂ := copy_exact a.reverse b [] [] []
  simp only [List.append_nil] at h₂
  have h₃ := restore_exact a.reverse [] [] [] b.reverse
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₃
  have h₄ := lift_division (Division.compute_exact true a.reverse b (by simpa using ha)) b []
  simp only [Division.selected, ↓reduceIte, dividerCfg_final] at h₄
  have h₅ := rotateA_exact [] [] (GcdBits.remainder a b) b []
  simp only [List.append_nil] at h₅
  have h₆ := rotateR_exact b.reverse [] (GcdBits.remainder a b) []
  simp only [List.append_nil] at h₆
  have h₇ := restoreR_exact b.reverse [] (GcdBits.remainder a b).reverse
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₇
  have h := (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇
  convert h using 1
  simp [cycleTime]
  omega

/-- A mathematical fuel parameter indexes a proved prefix of the unbounded loop;
it is never stored or decremented by the machine. -/
def loopTime : ℕ → List Bool → List Bool → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => if b = [] then 0 else cycleTime a b + loopTime n b (GcdBits.remainder a b)

/-- Every binary Euclidean recurrence prefix is realized by the same finite machine. -/
theorem loop_exact (n : ℕ) (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    Runs (cfg (some .loop) a.reverse b [] [] [])
      (cfg (some .loop) (GcdBits.loop n a b).1.reverse (GcdBits.loop n a b).2 [] [] [])
      (loopTime n a b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    by_cases hz : b = []
    · subst b
      simp only [GcdBits.loop, ↓reduceIte, loopTime]
      rfl
    · have h := (cycle_exact a b ha hz).trans
        (ih b (GcdBits.remainder a b) hb (GcdBits.canonical_remainder a b hb))
      simpa [GcdBits.loop, loopTime, hz, Nat.add_comm] using h

/-- Uniform per-iteration cost in a bound on the two live operand lengths. -/
theorem cycleTime_le (a b : List Bool) (hb : Canonical b) (s : ℕ)
    (hlen : a.length + b.length ≤ s) : cycleTime a b ≤ 3 * s ^ 2 + 13 * s + 10 := by
  have hd := Division.computeTime_le true a.reverse b
  simp only [List.length_reverse] at hd
  have hr := GcdBits.remainder_length_le a b hb
  have hp : (3 * (a.length + b.length) + 7) * a.length ≤ (3 * s + 7) * s :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold cycleTime
  calc
    _ ≤ (3 * s + 7) * s + 6 * s + 10 := by omega
    _ = 3 * s ^ 2 + 13 * s + 10 := by ring

/-- No intermediate bit-length growth is hidden in the sum of remainder calls. -/
theorem loopTime_le (n : ℕ) (a b : List Bool) (ha : Canonical a) (hb : Canonical b)
    (s : ℕ) (hlen : a.length + b.length ≤ s) :
    loopTime n a b ≤ n * (3 * s ^ 2 + 13 * s + 10) := by
  induction n generalizing a b with
  | zero => simp [loopTime]
  | succ n ih =>
    by_cases hz : b = []
    · simp [loopTime, hz]
    · have hc := cycleTime_le a b hb s hlen
      have hr := GcdBits.remainder_length_le a b hb
      have ht := ih b (GcdBits.remainder a b) hb (GcdBits.canonical_remainder a b hb) (by omega)
      simp only [loopTime, hz, ↓reduceIte]
      simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hc ht

/-- A fixed cubic dominates linear many quadratic remainder computations. -/
theorem polynomial_bound (s : ℕ) :
    (2 * s + 2) * (3 * s ^ 2 + 13 * s + 10) + s + 2 ≤ 64 * (s + 1) ^ 3 := by
  ring_nf
  omega

/-- Exact total transition count, with the proved bit-length fuel selecting enough
iterations of the same fixed, counter-free machine. -/
def computeTime (a b : List Bool) : ℕ :=
  loopTime (GcdBits.fuel a b) a b + (GcdBits.gcdBits a b).length + 2

theorem computeTime_le (a b : List Bool) (ha : Canonical a) (hb : Canonical b) :
    computeTime a b ≤ 64 * (a.length + b.length + 1) ^ 3 := by
  have ht := loopTime_le (GcdBits.fuel a b) a b ha hb (a.length + b.length) (Nat.le_refl _)
  have hs := GcdBits.loop_length_sum_le (GcdBits.fuel a b) a b ha hb
  have hp := polynomial_bound (a.length + b.length)
  unfold computeTime GcdBits.gcdBits
  simp only [GcdBits.fuel] at ht hs ⊢
  omega

/-- Genuine clean-halt gcd correctness, including either or both zero inputs. -/
theorem compute_encodeNat_exact (a b : ℕ) :
    Runs (cfg (some .loop) (encodeNat a).reverse (encodeNat b) [] [] [])
      (cfg none [] [] (encodeNat (Nat.gcd a b)) [] []) (computeTime (encodeNat a) (encodeNat b)) := by
  have h₁ := loop_exact (GcdBits.fuel (encodeNat a) (encodeNat b))
    (encodeNat a) (encodeNat b) (canonical_encodeNat a) (canonical_encodeNat b)
  rw [GcdBits.loop_fuel_encodeNat] at h₁
  have h := h₁.trans (done_exact (encodeNat (Nat.gcd a b)))
  simpa [computeTime, GcdBits.gcdBits_encodeNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def compute_timed (a b : ℕ) :
    StateTransition.EvalsToInTime computer.step
      (cfg (some .loop) (encodeNat a).reverse (encodeNat b) [] [] [])
      (some (cfg none [] [] (encodeNat (Nat.gcd a b)) [] []))
      (64 * ((encodeNat a).length + (encodeNat b).length + 1) ^ 3) where
  steps := computeTime (encodeNat a) (encodeNat b)
  evals_in_steps := compute_encodeNat_exact a b
  steps_le_m := computeTime_le _ _ (canonical_encodeNat a) (canonical_encodeNat b)

/-- The source result agrees literally with the finite computer's clean output. -/
theorem cfg_halt (word : List Bool) : cfg none [] [] word [] [] = haltList computer word := by
  dsimp [cfg, haltList, computer, initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem outside_budget (label : OuterLabel) : TM2Cost.budget (outside label) ≤ 6 := by
  cases label <;> decide

theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 12 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineReturn.program, MachineReturn.budget_stmt] using
      Division.program_budget true label
  | inr label => exact (outside_budget label).trans (by decide)

@[simp] theorem stack_count : Fintype.card computer.K = 9 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 17 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.Gcd
