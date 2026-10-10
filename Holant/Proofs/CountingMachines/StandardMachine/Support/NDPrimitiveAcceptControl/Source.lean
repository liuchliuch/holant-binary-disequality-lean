import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveAcceptControl.Paths
import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveFrontend.Source

set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Source
open Turing Computability Holant.Complexity
open Program
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
def source : Programme w := programme w
theorem accepts_iff (word : List Bool) :
    Nonempty (Paths.Path w word) ↔ Nonempty (NDPrimitiveFrontend.Composition.Path w word) :=
  ⟨fun ⟨p⟩ => ⟨Paths.backward w word p⟩,fun ⟨p⟩ => ⟨Paths.forward w word p⟩⟩
def clock : Polynomial ℕ := NDPrimitiveFrontend.Composition.clock w+Polynomial.C 2
theorem clock_eval (word : List Bool) : (clock w).eval word.length =
    (NDPrimitiveFrontend.Composition.clock w).eval word.length+2 := by simp [clock]
theorem time (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Paths.Trace w xs (initial w word) finalCfg) : xs.length ≤ (clock w).eval word.length := by
  rw [initial_lift] at h
  obtain ⟨pre,rest,oldEnd,hcut,hpre,hpost⟩ := Paths.first_exit w xs _ finalCfg h
  have hb := NDPrimitiveFrontend.Source.time w word pre oldEnd hpre
  change pre.length ≤ (NDPrimitiveFrontend.Composition.clock w).eval word.length at hb
  have hr : rest.length ≤ 2 := by
    rcases hpost with ⟨hz,he⟩ | ⟨ht,hr⟩
    · simp [hz]
    · exact (Paths.terminal_tail w rest oldEnd finalCfg ht hr).1
  rw [hcut,List.length_append,clock_eval]
  omega

/-- Actual observer completion, independent of the old verdict. Reject costs
one or two real write/move rows; accept costs exactly two. All are None. -/
theorem finish (a : Old.Cfg w) (ha : terminal w a.q = true) :
    ∃ n finalCfg, n ≤ 2 ∧ Paths.Trace w (List.replicate n none) (lift w a) finalCfg ∧
      (finalCfg.q = .inr .accept ∨ finalCfg.q = .inr .reject) ∧
      ∀ token, step w token finalCfg = none := by
  cases hg : headGood w a.q a.Tape.head
  · refine ⟨1,⟨.inr .reject,a.Tape⟩,by omega,?_,Or.inr rfl,reject_stops w _⟩
    exact ⟨_,by simpa [hg] using entry_step w a ha,rfl⟩
  · by_cases hb : (a.Tape.move .right).head = default
    · refine ⟨2,⟨.inr .accept,a.Tape.move .right⟩,by omega,?_,Or.inl rfl,accept_stops w _⟩
      exact Paths.accept_rows w a ha hg (by simpa [Tape.move] using hb)
    · refine ⟨2,⟨.inr .reject,a.Tape.move .right⟩,by omega,?_,Or.inr rfl,reject_stops w _⟩
      exact ⟨⟨.inr .probe,a.Tape.move .right⟩,by simpa [hg] using entry_step w a ha,
        _,by simpa only [if_neg hb] using probe_step w (a.Tape.move .right),rfl⟩

theorem prefix_completion (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Paths.Trace w xs (initial w word) finalCfg) :
    ∃ rest endCfg, Paths.Trace w rest finalCfg endCfg ∧
      (endCfg.q = .inr .accept ∨ endCfg.q = .inr .reject) ∧
      (∀ token, step w token endCfg = none) ∧ (xs++rest).length ≤ (clock w).eval word.length := by
  have hstart := h
  rw [initial_lift] at hstart
  obtain ⟨pre,remaining,oldEnd,hcut,hpre,hpost⟩ := Paths.first_exit w xs _ finalCfg hstart
  rcases hpost with ⟨hz,he⟩ | ⟨ht,hremaining⟩
  · obtain ⟨oldRest,c,hrest,hh,hbound⟩ := NDPrimitiveFrontend.Composition.prefix_completion w word pre oldEnd hpre
    have ht : terminal w (Old.lift w (Native.embed (machine w) c)).q = true := (terminal_native w _).mpr hh
    obtain ⟨n,endCfg,hn,hfinish,hcontrol,hstop⟩ := finish w _ ht
    have hrun := Paths.lift_trace w oldRest oldEnd _ hrest
    have hr := Paths.append w oldRest (List.replicate n none) (lift w oldEnd) _ endCfg hrun hfinish
    have hr' : Paths.Trace w (oldRest++List.replicate n none) finalCfg endCfg := he.symm ▸ hr
    exact ⟨oldRest++List.replicate n none,endCfg,hr',hcontrol,hstop,
      time w word _ _ (Paths.append w xs _ _ finalCfg _ h hr')⟩
  · obtain ⟨n,endCfg,hn,hfinish,hcontrol,hstop⟩ := finish w oldEnd ht
    have hlog := (Paths.terminal_tail w remaining oldEnd finalCfg ht hremaining).2
    obtain ⟨rest,hrestword,hr⟩ := Paths.deterministic_prefix w n remaining _ endCfg finalCfg hfinish hstop hremaining hlog
    exact ⟨rest,endCfg,hr,hcontrol,hstop,time w word _ _ (Paths.append w xs _ _ finalCfg _ h hr)⟩
theorem deadline (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Paths.Trace w xs (initial w word) finalCfg) (hlen : xs.length = (clock w).eval word.length) :
    (finalCfg.q = .inr .accept ∨ finalCfg.q = .inr .reject) ∧ ∀ token, step w token finalCfg = none := by
  obtain ⟨rest,endCfg,hr,hcontrol,hstop,hbound⟩ := prefix_completion w word xs finalCfg h
  have hz : rest.length = 0 := by simp only [List.length_append] at hbound; omega
  have he := List.length_eq_zero_iff.mp hz
  subst rest
  change finalCfg = endCfg at hr
  exact hr.symm ▸ ⟨hcontrol,hstop⟩

abbrev Within := NDPrimitiveFrontend.Source.Within w
def spacePolynomial : Polynomial ℕ := Polynomial.X+clock w
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
            exact NDPrimitiveFrontend.Source.within_move w R a.Tape d h
        | write s =>
            have he : (⟨next,a.Tape.write s⟩ : Cfg w) = b := Option.some.inj (by simpa [TM0.step,hm] using ht)
            subst b
            exact NDPrimitiveFrontend.Source.within_mono w R (R+1) _
              (NDPrimitiveFrontend.Source.within_write w R a.Tape s h) (Nat.le_add_right _ 1)
  cases token with
  | none =>
      cases hc : choose w a.q
      · exact selected false (by simpa [step,hc] using hs)
      · simp [step,hc] at hs
  | some bit =>
      cases hc : choose w a.q
      · simp [step,hc] at hs
      · exact selected bit (by simpa [step,hc] using hs)
theorem trace_space (xs : List (Option Bool)) (a b : Cfg w) (h : Paths.Trace w xs a b)
    (R : ℕ) (hs : Within w R a.Tape) : Within w (R+xs.length) b.Tape := by
  induction xs generalizing a R with
  | nil => change a = b at h; subst b; simpa using hs
  | cons token tokens ih =>
      obtain ⟨next,he,hr⟩ := h
      simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih next hr (R+1) (step_space w token a next he R hs)
theorem prefix_space (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Paths.Trace w xs (initial w word) finalCfg) : Within w ((spacePolynomial w).eval word.length) finalCfg.Tape := by
  have hi : Within w word.length (initial w word).Tape := NDPrimitiveFrontend.Source.initial_space w word
  have hs := trace_space w xs _ finalCfg h word.length hi
  apply NDPrimitiveFrontend.Source.within_mono w _ _ _ hs
  simpa [spacePolynomial] using Nat.add_le_add_left (time w word xs finalCfg h) word.length

theorem witness_source (a : α) :
    Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃ Paths.Path w (TotalRawSource.encodedInput w a)) ∧
    Paths.count w (TotalRawSource.encodedInput w a) = f a ∧
    ∀ (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w),
      Paths.Trace w xs (initial w word) finalCfg →
      xs.length ≤ (clock w).eval word.length ∧ Within w ((spacePolynomial w).eval word.length) finalCfg.Tape ∧
      ∃ rest endCfg, Paths.Trace w rest finalCfg endCfg ∧
        (endCfg.q = .inr .accept ∨ endCfg.q = .inr .reject) ∧
        (∀ token, step w token endCfg = none) ∧ (xs++rest).length ≤ (clock w).eval word.length :=
  ⟨⟨Paths.originalPathsEquiv w a⟩,Paths.encoded_count w a,
    fun word xs finalCfg h => ⟨time w word xs finalCfg h,prefix_space w word xs finalCfg h,prefix_completion w word xs finalCfg h⟩⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Source
