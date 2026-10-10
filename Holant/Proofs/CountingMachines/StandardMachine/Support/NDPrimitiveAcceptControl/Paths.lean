import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveAcceptControl.Observation

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Actual unsegmented paths endpoint in a designated finite
accepting label, with no tape predicate in the accepting-path definition.
Only the observer's actual two None rows are appended to old accepting paths. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Paths
open Turing Computability Holant.Complexity
open Program
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
def Trace : List (Option Bool) → Cfg w → Cfg w → Prop
  | [],a,b => a = b
  | token::tokens,a,b => ∃ next, step w token a = some next ∧ Trace tokens next b
theorem append (xs ys : List (Option Bool)) (a mid b : Cfg w)
    (hx : Trace w xs a mid) (hy : Trace w ys mid b) : Trace w (xs++ys) a b := by
  induction xs generalizing a with
  | nil => change a = mid at hx; subst a; exact hy
  | cons token tokens ih => obtain ⟨next,hs,hr⟩ := hx; exact ⟨next,hs,ih next hr⟩
theorem stopped_trace (xs : List (Option Bool)) (a b : Cfg w)
    (ha : ∀ token, step w token a = none) (h : Trace w xs a b) : xs = [] ∧ a = b := by
  cases xs with
  | nil => exact ⟨rfl,h⟩
  | cons token tokens => obtain ⟨next,hs,hr⟩ := h; rw [ha token] at hs; cases hs
theorem lift_trace (xs : List (Option Bool)) (a b : Old.Cfg w)
    (h : NDPrimitiveFrontend.Composition.Trace w xs a b) : Trace w xs (lift w a) (lift w b) := by
  induction xs generalizing a with
  | nil => exact h ▸ rfl
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := h
      have ha : terminal w a.q = false := by
        cases hh : terminal w a.q
        · rfl
        · rw [terminal_old_stops w a hh token] at hs; cases hs
      exact ⟨lift w next,by rw [active_step w token a ha,hs]; rfl,ih next hr⟩

theorem first_exit (xs : List (Option Bool)) (a : Old.Cfg w) (finalCfg : Cfg w)
    (h : Trace w xs (lift w a) finalCfg) :
    ∃ pre rest oldEnd, xs = pre++rest ∧ NDPrimitiveFrontend.Composition.Trace w pre a oldEnd ∧
      ((rest = [] ∧ finalCfg = lift w oldEnd) ∨
        (terminal w oldEnd.q = true ∧ Trace w rest (lift w oldEnd) finalCfg)) := by
  induction xs generalizing a with
  | nil => exact ⟨[],[],a,rfl,rfl,Or.inl ⟨rfl,h.symm⟩⟩
  | cons token tokens ih =>
      cases ht : terminal w a.q
      · obtain ⟨next,hs,hr⟩ := h
        rw [active_step w token a ht] at hs
        cases he : Old.step w token a with
        | none => simp [he] at hs
        | some oldNext =>
            have hn : lift w oldNext = next := Option.some.inj (by simpa [he] using hs)
            obtain ⟨pre,rest,oldEnd,hcut,hpre,hpost⟩ := ih oldNext (hn.symm ▸ hr)
            exact ⟨token::pre,rest,oldEnd,by simp [hcut],⟨oldNext,he,hpre⟩,hpost⟩
      · exact ⟨[],token::tokens,a,rfl,rfl,Or.inr ⟨ht,h⟩⟩

theorem terminal_tail (xs : List (Option Bool)) (a : Old.Cfg w) (finalCfg : Cfg w)
    (ha : terminal w a.q = true) (h : Trace w xs (lift w a) finalCfg) :
    xs.length ≤ 2 ∧ xs.filterMap id = [] := by
  cases xs with
  | nil => simp
  | cons token tokens =>
      obtain ⟨next,hs,hr⟩ := h
      cases token with
      | some bit => rw [entry_no_choice w a ha bit] at hs; cases hs
      | none =>
          cases hg : headGood w a.q a.Tape.head
          · have hn : next = ⟨.inr .reject,a.Tape⟩ :=
              (Option.some.inj (by simpa [entry_step w a ha,hg] using hs)).symm
            subst next
            obtain ⟨hz,he⟩ := stopped_trace w tokens _ _ (reject_stops w _) hr
            simp [hz]
          · have hn : next = ⟨.inr .probe,a.Tape.move .right⟩ :=
              (Option.some.inj (by simpa [entry_step w a ha,hg] using hs)).symm
            subst next
            cases tokens with
            | nil => simp
            | cons token tokens =>
                obtain ⟨last,hl,hrest⟩ := hr
                cases token with
                | some bit => rw [phase_no_choice w .probe _ bit] at hl; cases hl
                | none =>
                    have hl' := Option.some.inj ((probe_step w (a.Tape.move .right)).symm.trans hl)
                    by_cases hb : (a.Tape.move .right).head = default
                    · have he : last = ⟨.inr .accept,a.Tape.move .right⟩ := by simpa only [if_pos hb] using hl'.symm
                      rw [he] at hrest
                      obtain ⟨hz,hend⟩ := stopped_trace w tokens _ _ (accept_stops w _) hrest
                      simp [hz]
                    · have he : last = ⟨.inr .reject,a.Tape.move .right⟩ := by simpa only [if_neg hb] using hl'.symm
                      rw [he] at hrest
                      obtain ⟨hz,hend⟩ := stopped_trace w tokens _ _ (reject_stops w _) hrest
                      simp [hz]

theorem terminal_accept (xs : List (Option Bool)) (a : Old.Cfg w) (T : Tape (Symbol w))
    (ha : terminal w a.q = true) (h : Trace w xs (lift w a) ⟨.inr .accept,T⟩) :
    xs = [none,none] ∧ headGood w a.q a.Tape.head = true ∧ a.Tape.right.head = default := by
  cases xs with
  | nil => change lift w a = _ at h; have hq := congrArg TM0.Cfg.q h; cases hq
  | cons token tokens =>
      obtain ⟨next,hs,hr⟩ := h
      cases token with
      | some bit => rw [entry_no_choice w a ha bit] at hs; cases hs
      | none =>
          cases hg : headGood w a.q a.Tape.head
          · have hn : next = ⟨.inr .reject,a.Tape⟩ :=
              (Option.some.inj (by simpa [entry_step w a ha,hg] using hs)).symm
            subst next
            have he := (stopped_trace w tokens _ _ (reject_stops w _) hr).2
            have hq := congrArg TM0.Cfg.q he; cases hq
          · have hn : next = ⟨.inr .probe,a.Tape.move .right⟩ :=
              (Option.some.inj (by simpa [entry_step w a ha,hg] using hs)).symm
            subst next
            cases tokens with
            | nil => change (⟨.inr .probe,a.Tape.move .right⟩ : Cfg w) = _ at hr; have hq := congrArg TM0.Cfg.q hr; cases hq
            | cons token tokens =>
                obtain ⟨last,hl,hrest⟩ := hr
                cases token with
                | some bit => rw [phase_no_choice w .probe _ bit] at hl; cases hl
                | none =>
                    have hl' := Option.some.inj ((probe_step w (a.Tape.move .right)).symm.trans hl)
                    by_cases hb : (a.Tape.move .right).head = default
                    · have he : last = ⟨.inr .accept,a.Tape.move .right⟩ := by simpa only [if_pos hb] using hl'.symm
                      rw [he] at hrest
                      have hz := (stopped_trace w tokens _ _ (accept_stops w _) hrest).1
                      exact ⟨by simp [hz],rfl,by simpa [Tape.move] using hb⟩
                    · have he : last = ⟨.inr .reject,a.Tape.move .right⟩ := by simpa only [if_neg hb] using hl'.symm
                      rw [he] at hrest
                      have he := (stopped_trace w tokens _ _ (reject_stops w _) hrest).2
                      have hq := congrArg TM0.Cfg.q he; cases hq
theorem accept_rows (a : Old.Cfg w) (ha : terminal w a.q = true)
    (hg : headGood w a.q a.Tape.head = true) (hb : a.Tape.right.head = default) :
    Trace w [none,none] (lift w a) ⟨.inr .accept,a.Tape.move .right⟩ := by
  refine ⟨⟨.inr .probe,a.Tape.move .right⟩,?_,_,?_,rfl⟩
  · simpa [hg] using entry_step w a ha
  · simpa [Tape.move,hb] using probe_step w (a.Tape.move .right)

theorem deterministic_prefix (n : ℕ) (xs : List (Option Bool)) (a b finalCfg : Cfg w)
    (hfull : Trace w (List.replicate n none) a b) (hb : ∀ token, step w token b = none)
    (h : Trace w xs a finalCfg) (hlog : xs.filterMap id = []) :
    ∃ rest, List.replicate n none = xs++rest ∧ Trace w rest finalCfg b := by
  induction n generalizing a xs with
  | zero =>
      change a = b at hfull
      subst a
      obtain ⟨hz,he⟩ := stopped_trace w xs b finalCfg hb h
      exact ⟨[],by simp [hz],he.symm⟩
  | succ n ih =>
      cases xs with
      | nil => change a = finalCfg at h; subst finalCfg; exact ⟨List.replicate (n+1) none,rfl,hfull⟩
      | cons token tokens =>
          obtain ⟨next,hs,hr⟩ := hfull
          obtain ⟨next',ht,hrest⟩ := h
          cases token with
          | some bit => simp at hlog
          | none =>
              have he : next = next' := Option.some.inj (hs.symm.trans ht)
              subst next'
              obtain ⟨rest,hcut,htrace⟩ := ih tokens next hr hrest (by simpa using hlog)
              exact ⟨rest,by simpa [List.replicate_succ] using congrArg (none :: ·) hcut,htrace⟩

abbrev Path (word : List Bool) := {xs : List (Option Bool) //
  ∃ T : Tape (Symbol w), Trace w xs (initial w word) ⟨.inr .accept,T⟩}
def forward (word : List Bool) (p : NDPrimitiveFrontend.Composition.Path w word) : Path w word :=
  ⟨p.val++[none,none],by
    obtain ⟨c,hc,hr⟩ := p.property
    let oldEnd := Old.lift w (Native.embed (machine w) c)
    have hl := (Observation.true_columns w c hc).1
    have ht : terminal w oldEnd.q = true := (terminal_native w _).mpr
      (NDPrimitiveDispatcher.Program.embed_halted (machine w) c hl)
    have hg := (Observation.observed_true_iff w _ c hc rfl).mpr hc
    exact ⟨oldEnd.Tape.move .right,by
      rw [initial_lift]
      exact append w _ _ _ _ _ (lift_trace w _ _ _ hr) (accept_rows w oldEnd ht hg.1 hg.2)⟩⟩
theorem backward_exists (word : List Bool) (p : Path w word) :
    ∃ q : NDPrimitiveFrontend.Composition.Path w word, p.val = q.val++[none,none] := by
  obtain ⟨T,hr⟩ := p.property
  change Trace w p.val (lift w (Old.initial w word)) ⟨.inr .accept,T⟩ at hr
  obtain ⟨pre,rest,oldEnd,hcut,hpre,hpost⟩ := first_exit w p.val (Old.initial w word) _ hr
  rcases hpost with ⟨hz,he⟩ | ⟨ht,hrest⟩
  · have hq := congrArg TM0.Cfg.q he; cases hq
  · obtain ⟨hrestword,hgood,hblank⟩ := terminal_accept w rest oldEnd T ht hrest
    obtain ⟨choices,c,hend,hencoded⟩ := Observation.actual_halt_encoding w word pre oldEnd hpre ht
    have hg := hend ▸ (show headGood w oldEnd.q oldEnd.Tape.head = true ∧ oldEnd.Tape.right.head = default from ⟨hgood,hblank⟩)
    have hc := (Observation.observed_true_iff w _ c hencoded (TotalRawSource.terminal_halts w word choices)).mp hg
    exact ⟨⟨pre,c,hc,hend ▸ hpre⟩,by simpa only [hrestword] using hcut⟩
def backward (word : List Bool) (p : Path w word) : NDPrimitiveFrontend.Composition.Path w word :=
  Classical.choose (backward_exists w word p)
def pathsEquiv (word : List Bool) : NDPrimitiveFrontend.Composition.Path w word ≃ Path w word where
  toFun := forward w word
  invFun := backward w word
  left_inv p := by
    apply Subtype.ext
    have hc := Classical.choose_spec (backward_exists w word (forward w word p))
    exact List.append_cancel_right hc.symm
  right_inv p := by
    apply Subtype.ext
    exact (Classical.choose_spec (backward_exists w word p)).symm
theorem forward_guesses (word : List Bool) (p : NDPrimitiveFrontend.Composition.Path w word) :
    (forward w word p).val.filterMap id = p.val.filterMap id := by simp [forward]
instance (word : List Bool) : Fintype (Path w word) :=
  Fintype.ofEquiv (NDPrimitiveFrontend.Composition.Path w word) (pathsEquiv w word)
def count (word : List Bool) : ℕ := Fintype.card (Path w word)
theorem raw_count (word : List Bool) : count w word = NDPrimitiveFrontend.Composition.count w word :=
  Fintype.card_congr (pathsEquiv w word).symm
def originalPathsEquiv (a : α) : ConventionalSharpPSource.AcceptedWitness w a ≃ Path w (TotalRawSource.encodedInput w a) :=
  (NDPrimitiveFrontend.Composition.originalPathsEquiv w a).trans (pathsEquiv w _)
theorem encoded_count (a : α) : count w (TotalRawSource.encodedInput w a) = f a :=
  (raw_count w _).trans (NDPrimitiveFrontend.Composition.encoded_count w a)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Paths
