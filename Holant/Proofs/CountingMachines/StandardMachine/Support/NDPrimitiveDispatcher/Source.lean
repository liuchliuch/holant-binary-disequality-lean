import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveDispatcher.Paths

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Sole finite ND TM0 primitive source. Its input is the
same actual compiler tape word trInit, its acceptance protocol the same clean
true output tape. A physical raw-Bool-to-trInit frontend and conversion to a
separate finite accept-control convention are NOT asserted by these receipts. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Source
open Turing Computability Holant.Complexity
open Program
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
abbrev machine := Paths.machine w
def source : Programme (machine w) := programme (machine w)
abbrev clock := Paths.clock w

theorem time (word : List Bool) (instructions : List (Option Bool)) (finalCfg : Cfg (machine w))
    (h : Runs.Trace (machine w) instructions (Paths.initial w word) finalCfg) :
    instructions.length ≤ (clock w).eval word.length := Paths.prefix_time w word instructions finalCfg h

/-- Each physical TM0 edge updates exactly its advertised move/write tape. -/
theorem step_space (token : Option Bool) (a b : Cfg (machine w))
    (hstep : step (machine w) token a = some b) (R : ℕ)
    (h : TapeMicrostepBudget.Within (machine w) R a.Tape) :
    TapeMicrostepBudget.Within (machine w) (R+1) b.Tape := by
  have chosen (bit : Bool) (hs : TM0.step (table (machine w) bit) a = some b) :
      TapeMicrostepBudget.Within (machine w) (R+1) b.Tape := by
    cases ht : table (machine w) bit a.q a.Tape.head with
    | none => simp [TM0.step,ht] at hs
    | some result =>
        rcases result with ⟨next,operation⟩
        cases operation with
        | move d =>
            have he : (⟨next,a.Tape.move d⟩ : Cfg (machine w)) = b :=
              Option.some.inj (by simpa [TM0.step,ht] using hs)
            subst b
            exact TapeMicrostepBudget.within_move (machine w) R a.Tape d h
        | write symbol =>
            have he : (⟨next,a.Tape.write symbol⟩ : Cfg (machine w)) = b :=
              Option.some.inj (by simpa [TM0.step,ht] using hs)
            subst b
            exact TapeMicrostepBudget.within_mono (machine w) R (R+1) _
              (TapeMicrostepBudget.within_write (machine w) R a.Tape symbol h) (Nat.le_add_right _ 1)
  cases token with
  | none =>
      cases hc : choose (machine w) a.q
      · exact chosen false (by simpa [step,hc] using hstep)
      · simp [step,hc] at hstep
  | some bit =>
      cases hc : choose (machine w) a.q
      · simp [step,hc] at hstep
      · exact chosen bit (by simpa [step,hc] using hstep)

def spacePolynomial : Polynomial ℕ := Polynomial.X+clock w
theorem space_eval (word : List Bool) : (spacePolynomial w).eval word.length = word.length+(clock w).eval word.length := by
  simp [spacePolynomial]
theorem trace_space (instructions : List (Option Bool)) (a b : Cfg (machine w))
    (ht : Runs.Trace (machine w) instructions a b) (R : ℕ)
    (h : TapeMicrostepBudget.Within (machine w) R a.Tape) :
    TapeMicrostepBudget.Within (machine w) (R+instructions.length) b.Tape := by
  induction instructions generalizing a R with
  | nil => change a = b at ht; subst b; simpa using h
  | cons token tokens ih =>
      obtain ⟨mid,hs,hr⟩ := ht
      have hm := step_space w token a mid hs R h
      simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih mid hr (R+1) hm

theorem prefix_space (word : List Bool) (instructions : List (Option Bool)) (finalCfg : Cfg (machine w))
    (h : Runs.Trace (machine w) instructions (Paths.initial w word) finalCfg) :
    TapeMicrostepBudget.Within (machine w) ((spacePolynomial w).eval word.length) finalCfg.Tape := by
  have hs := trace_space w instructions _ finalCfg h word.length (TapeMicrostepBudget.initial_space w word)
  rw [space_eval]
  exact TapeMicrostepBudget.within_mono (machine w) _ _ _ hs (Nat.add_le_add_left (time w word instructions finalCfg h) _)

def controlWidth : ℕ := TapeMicrostepBudget.CellBits.width (Control (machine w))
def snapshot (R : ℕ) (c : Cfg (machine w)) : List Bool :=
  TapeMicrostepBudget.CellBits.code c.q++TapeMicrostepBudget.CellBits.word
    (List.ofFn (TapeMicrostepBudget.window (machine w) R c.Tape))
theorem snapshot_length (R : ℕ) (c : Cfg (machine w)) :
    (snapshot w R c).length = controlWidth w+TapeMicrostepBudget.symbolWidth (machine w)*(2*R+1) := by
  simp [snapshot,controlWidth,TapeMicrostepBudget.symbolWidth]
theorem snapshot_faithful (R : ℕ) (a b : Cfg (machine w))
    (ha : TapeMicrostepBudget.Within (machine w) R a.Tape)
    (hb : TapeMicrostepBudget.Within (machine w) R b.Tape) (h : snapshot w R a = snapshot w R b) : a = b := by
  have hc : TapeMicrostepBudget.CellBits.code a.q = TapeMicrostepBudget.CellBits.code b.q := by
    have hp := congrArg (List.take (controlWidth w)) h
    simpa [snapshot,controlWidth,List.take_append] using hp
  have hw : TapeMicrostepBudget.CellBits.word (List.ofFn (TapeMicrostepBudget.window (machine w) R a.Tape)) =
      TapeMicrostepBudget.CellBits.word (List.ofFn (TapeMicrostepBudget.window (machine w) R b.Tape)) :=
    List.append_cancel_left (by simpa only [snapshot,hc] using h)
  have ht := TapeMicrostepBudget.window_faithful (machine w) R a.Tape b.Tape ha hb
    (List.ofFn_injective (TapeMicrostepBudget.CellBits.word_injective hw))
  have hq := TapeMicrostepBudget.CellBits.code_injective hc
  cases a; cases b; cases hq; cases ht; rfl
def bitsPolynomial : Polynomial ℕ := Polynomial.C (controlWidth w)+
  Polynomial.C (TapeMicrostepBudget.symbolWidth (machine w))*(Polynomial.C 2*spacePolynomial w+Polynomial.C 1)
theorem prefix_bits (word : List Bool) (instructions : List (Option Bool)) (finalCfg : Cfg (machine w))
    (h : Runs.Trace (machine w) instructions (Paths.initial w word) finalCfg) :
    (snapshot w ((spacePolynomial w).eval word.length) finalCfg).length ≤ (bitsPolynomial w).eval word.length := by
  rw [snapshot_length]
  simp [bitsPolynomial]

/-- Unique source capstone. Both the all-pre physical clock and the
accepted-path bijection/count are internally produced for the SAME table. -/
theorem witness_source (a : α) :
    Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃ Paths.Path w (TotalRawSource.encodedInput w a)) ∧
    Paths.count w (TotalRawSource.encodedInput w a) = f a ∧
    ∀ (word : List Bool) (instructions : List (Option Bool)) (finalCfg : Cfg (machine w)),
      Runs.Trace (machine w) instructions (Paths.initial w word) finalCfg →
      instructions.length ≤ (clock w).eval word.length ∧
      TapeMicrostepBudget.Within (machine w) ((spacePolynomial w).eval word.length) finalCfg.Tape ∧
      (snapshot w ((spacePolynomial w).eval word.length) finalCfg).length ≤ (bitsPolynomial w).eval word.length :=
  ⟨⟨Paths.originalPathsEquiv w a⟩,Paths.encoded_count w a,
    fun word instructions finalCfg h => ⟨time w word instructions finalCfg h,prefix_space w word instructions finalCfg h,
      prefix_bits w word instructions finalCfg h⟩⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Source
