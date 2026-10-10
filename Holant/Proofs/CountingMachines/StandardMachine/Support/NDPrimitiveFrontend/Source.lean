import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveFrontend.Composition

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Sole raw-input source. Original Bool letters are the
raw symbols of the finite tape alphabet (false is not blank). The actual
frontend, rather than the caller, writes/clears its markers and produces
trInit. Acceptance still uses the existing clean true tape protocol; no new
finite accept-control convention or conventional #P equivalence is asserted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Source
open Turing Computability Holant.Complexity
open Program
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
def source : Programme w := programme w
abbrev clock := Composition.clock w
theorem initializes (word : List Bool) : Execution.Rows w (Execution.steps word.length)
    (initial w word) (lift w (NDPrimitiveDispatcher.Paths.initial w word)) := Execution.prepare w word
theorem time (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Composition.Trace w xs (initial w word) finalCfg) : xs.length ≤ (clock w).eval word.length :=
  Composition.prefix_time w word xs finalCfg h

theorem prefix_completion (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Composition.Trace w xs (initial w word) finalCfg) :
    ∃ rest final, Composition.Trace w rest finalCfg final ∧
      (∀ token, step w token final = none) ∧ (xs++rest).length ≤ (clock w).eval word.length := by
  obtain ⟨rest,c,hr,hh,hbound⟩ := Composition.prefix_completion w word xs finalCfg h
  exact ⟨rest,_,hr,Composition.lift_halted w _ hh,hbound⟩
theorem deadline (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Composition.Trace w xs (initial w word) finalCfg) (hlen : xs.length = (clock w).eval word.length) :
    ∀ token, step w token finalCfg = none := by
  obtain ⟨rest,final,hr,hh,hbound⟩ := prefix_completion w word xs finalCfg h
  have hz : rest.length = 0 := by simp only [List.length_append] at hbound; omega
  have he : rest = [] := List.length_eq_zero_iff.mp hz
  subst rest
  change finalCfg = final at hr
  exact hr.symm ▸ hh

def Within (R : ℕ) (T : Tape (Symbol w)) : Prop :=
  ∀ i : ℤ, i < -(R : ℤ) ∨ (R : ℤ) < i → T.nth i = default
theorem within_mono (R U : ℕ) (T : Tape (Symbol w)) (h : Within w R T) (hRU : R ≤ U) : Within w U T := by
  intro i hi
  exact h i (by omega)
theorem within_move (R : ℕ) (T : Tape (Symbol w)) (d : Dir) (h : Within w R T) : Within w (R+1) (T.move d) := by
  intro i hi
  cases d
  · rw [Tape.move_left_nth]; exact h (i-1) (by omega)
  · rw [Tape.move_right_nth]; exact h (i+1) (by omega)
theorem within_write (R : ℕ) (T : Tape (Symbol w)) (a : Symbol w) (h : Within w R T) : Within w R (T.write a) := by
  intro i hi
  rw [Tape.write_nth,if_neg (by omega : i ≠ 0)]
  exact h i hi
theorem initial_space (word : List Bool) : Within w word.length (initial w word).Tape := by
  intro i hi
  cases i with
  | ofNat n =>
      have hi' : (n : ℤ) < -(word.length : ℤ) ∨ (word.length : ℤ) < (n : ℤ) := hi
      have hn : (rawWord w word).length ≤ n := by simp only [rawWord,List.length_map]; omega
      simp [initial,TM0.init,Tape.mk₁,Tape.mk₂,Tape.mk'_nth_nat,ListBlank.nth_mk,List.getI_eq_default (rawWord w word) hn]
  | negSucc n =>
      change (ListBlank.mk ([] : List (Symbol w))).nth n = default
      rw [ListBlank.nth_mk,List.getI_nil]

theorem step_space (token : Option Bool) (a b : Cfg w) (hs : step w token a = some b) (R : ℕ)
    (h : Within w R a.Tape) : Within w (R+1) b.Tape := by
  have selected (bit : Bool) (ht : TM0.step (table w bit) a = some b) : Within w (R+1) b.Tape := by
    cases hm : table w bit a.q a.Tape.head with
    | none => simp [TM0.step,hm] at ht
    | some result =>
        rcases result with ⟨next,op⟩
        cases op with
        | move d =>
            have he : (⟨next,a.Tape.move d⟩ : Cfg w) = b := Option.some.inj (by simpa [TM0.step,hm] using ht)
            subst b
            exact within_move w R a.Tape d h
        | write s =>
            have he : (⟨next,a.Tape.write s⟩ : Cfg w) = b := Option.some.inj (by simpa [TM0.step,hm] using ht)
            subst b
            exact within_mono w R (R+1) _ (within_write w R a.Tape s h) (Nat.le_add_right _ 1)
  cases token with
  | none =>
    cases hc : choose w a.q
    · exact selected false (by simpa [step,hc] using hs)
    · simp [step,hc] at hs
  | some bit =>
    cases hc : choose w a.q
    · simp [step,hc] at hs
    · exact selected bit (by simpa [step,hc] using hs)

def spacePolynomial : Polynomial ℕ := Polynomial.X+clock w
theorem trace_space (xs : List (Option Bool)) (a b : Cfg w) (h : Composition.Trace w xs a b)
    (R : ℕ) (hs : Within w R a.Tape) : Within w (R+xs.length) b.Tape := by
  induction xs generalizing a R with
  | nil => change a = b at h; subst b; simpa using hs
  | cons token tokens ih =>
      obtain ⟨next,he,hr⟩ := h
      simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih next hr (R+1) (step_space w token a next he R hs)
theorem prefix_space (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Composition.Trace w xs (initial w word) finalCfg) : Within w ((spacePolynomial w).eval word.length) finalCfg.Tape := by
  have hs := trace_space w xs _ finalCfg h word.length (initial_space w word)
  apply within_mono w _ _ _ hs
  simpa [spacePolynomial] using Nat.add_le_add_left (time w word xs finalCfg h) word.length

/-- Actual one-move/one-write displacement observer, including frontend
fence/EOF scans. It is not an encoded input or a transition opcode. -/
def displacement : List (Option Bool) → Cfg w → ℤ
  | [],_ => 0
  | token::tokens,c =>
      let bit := token.getD false
      match table w bit c.q c.Tape.head,step w token c with
      | some (_, .move .left),some next => -1+displacement tokens next
      | some (_, .move .right),some next => 1+displacement tokens next
      | some (_, .write _),some next => displacement tokens next
      | _,_ => 0
theorem displacement_bound (xs : List (Option Bool)) (a b : Cfg w) (h : Composition.Trace w xs a b) :
    -(xs.length : ℤ) ≤ displacement w xs a ∧ displacement w xs a ≤ (xs.length : ℤ) := by
  induction xs generalizing a with
  | nil => simp [displacement]
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := h
      have hb := ih next hr
      cases ht : table w (token.getD false) a.q a.Tape.head with
      | none => simp [displacement,ht,hs]; omega
      | some result =>
          rcases result with ⟨control,op⟩
          cases op with
          | move d => cases d <;> simp only [displacement,ht,hs,List.length_cons,Nat.cast_add,Nat.cast_one] <;> omega
          | write s => simp only [displacement,ht,hs,List.length_cons,Nat.cast_add,Nat.cast_one]; omega
theorem visited (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Composition.Trace w xs (initial w word) finalCfg) :
    ∃ i : Fin (2*(clock w).eval word.length+1), (i.val : ℤ)-(((clock w).eval word.length : ℕ) : ℤ) =
      displacement w xs (initial w word) := by
  have hb := displacement_bound w xs _ finalCfg h
  have ht := time w word xs finalCfg h
  apply TapeMicrostepBudget.bounded_position
  omega

theorem witness_source (a : α) :
    Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃ Composition.Path w (TotalRawSource.encodedInput w a)) ∧
    Composition.count w (TotalRawSource.encodedInput w a) = f a ∧
    (∀ word : List Bool, Execution.Rows w (Execution.steps word.length) (initial w word)
      (lift w (NDPrimitiveDispatcher.Paths.initial w word))) ∧
    ∀ (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w),
      Composition.Trace w xs (initial w word) finalCfg →
      xs.length ≤ (clock w).eval word.length ∧ Within w ((spacePolynomial w).eval word.length) finalCfg.Tape ∧
      ∃ rest final, Composition.Trace w rest finalCfg final ∧
        (∀ token, step w token final = none) ∧ (xs++rest).length ≤ (clock w).eval word.length :=
  ⟨⟨Composition.originalPathsEquiv w a⟩,Composition.encoded_count w a,initializes w,
    fun word xs finalCfg h => ⟨time w word xs finalCfg h,prefix_space w word xs finalCfg h,prefix_completion w word xs finalCfg h⟩⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Source
