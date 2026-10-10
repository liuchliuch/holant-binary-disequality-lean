import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveFrontend.Execution

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Deterministic physical preparation followed by the
installed unchanged native dispatcher. Projection is only a proof observer,
never a transition-table opcode or a supplied decoder/simulation premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Composition
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
theorem rows_trace (n : ℕ) (a b : Cfg w) (h : Execution.Rows w n a b) : Trace w (List.replicate n none) a b := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih => obtain ⟨next,hs,hr⟩ := h; exact ⟨next,hs,ih next hr⟩

theorem right_stays_right (token : Option Bool) (a b : Cfg w)
    (ha : a.q.isLeft = false) (h : step w token a = some b) : b.q.isLeft = false := by
  rcases a with ⟨control,T⟩
  cases control with
  | inl s => simp at ha
  | inr s =>
      have chosen (bit : Bool) (hs : TM0.step (table w bit) ⟨.inr s,T⟩ = some b) : b.q.isLeft = false := by
        cases hh : T.head <;> simp only [table,TM0.step,hh,Option.bind_none,Option.map_none] at hs <;> try contradiction
        case native a =>
          cases ht : Native.table (machine w) bit s a with
          | none => simp only [ht,Option.map_none,Option.bind_none] at hs; cases hs
          | some result =>
              rcases result with ⟨next,operation⟩
              have he := Option.some.inj (by simpa only [ht,Option.map_some,Option.bind_some] using hs)
              cases operation <;> cases he <;> rfl
      cases token with
      | none =>
          cases hc : choose w (.inr s)
          · exact chosen false (by simpa [step,hc] using h)
          · simp [step,hc] at h
      | some bit =>
          cases hc : choose w (.inr s)
          · simp [step,hc] at h
          · exact chosen bit (by simpa [step,hc] using h)

theorem rows_front (n : ℕ) (a b : Cfg w) (h : Execution.Rows w n a b) (hb : b.q.isLeft = true) :
    a.q.isLeft = true := by
  induction n generalizing a with
  | zero => exact h.symm ▸ hb
  | succ n ih =>
      obtain ⟨next,hs,hr⟩ := h
      have hn := ih next hr
      cases ha : a.q.isLeft
      · have hf := right_stays_right w none a next ha hs; rw [hn] at hf; cases hf
      · rfl

theorem front_edge (token : Option Bool) (a b c : Cfg w) (ha : a.q.isLeft = true)
    (hb : step w none a = some b) (hc : step w token a = some c) : token = none ∧ b = c := by
  rcases a with ⟨control,T⟩
  cases control with
  | inr s => simp at ha
  | inl s =>
    cases token with
    | some bit => rw [front_no_choice w s T bit] at hc; cases hc
    | none => exact ⟨rfl,Option.some.inj (hb.symm.trans hc)⟩

/-- An arbitrary actual pre either remains inside the genuinely frontend
part, or contains exactly its unique None transcript and a real suffix. -/
theorem before_match (n : ℕ) (a before finalCfg : Cfg w)
    (hp : Execution.Rows w n a before) (hb : before.q.isLeft = true)
    (xs : List (Option Bool)) (h : Trace w xs a finalCfg) :
    (xs.length ≤ n ∧ finalCfg.q.isLeft = true) ∨
      ∃ rest, xs = List.replicate n none++rest ∧ Trace w rest before finalCfg := by
  induction n generalizing a xs with
  | zero => change a = before at hp; subst a; exact Or.inr ⟨xs,rfl,h⟩
  | succ n ih =>
      obtain ⟨next,hs,hr⟩ := hp
      have ha := rows_front w (n+1) a before ⟨next,hs,hr⟩ hb
      cases xs with
      | nil => change a = finalCfg at h; subst finalCfg; exact Or.inl ⟨by simp,ha⟩
      | cons token tokens =>
          obtain ⟨next',ht,hrest⟩ := h
          obtain ⟨he,hn⟩ := front_edge w token a next next' ha hs ht
          subst token
          subst next'
          rcases ih next hr tokens hrest with ⟨hlen,hfront⟩ | ⟨rest,hcut,htrace⟩
          · exact Or.inl ⟨by simpa using Nat.add_le_add_right hlen 1,hfront⟩
          · exact Or.inr ⟨rest,by simp [List.replicate_succ,hcut],htrace⟩

theorem before_completion (n : ℕ) (a before finalCfg : Cfg w)
    (hp : Execution.Rows w n a before) (hb : before.q.isLeft = true)
    (xs : List (Option Bool)) (h : Trace w xs a finalCfg) (hlen : xs.length ≤ n) :
    ∃ rest, List.replicate n none = xs++rest ∧ Trace w rest finalCfg before := by
  induction n generalizing a xs with
  | zero =>
      have hz : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      change a = finalCfg at h
      change a = before at hp
      exact ⟨[],rfl,h.symm.trans hp⟩
  | succ n ih =>
      cases xs with
      | nil =>
          change a = finalCfg at h
          subst finalCfg
          exact ⟨List.replicate (n+1) none,rfl,rows_trace w _ _ _ hp⟩
      | cons token tokens =>
          obtain ⟨next,hs,hr⟩ := hp
          obtain ⟨next',ht,hrest⟩ := h
          have ha := rows_front w (n+1) a before ⟨next,hs,hr⟩ hb
          obtain ⟨he,hn⟩ := front_edge w token a next next' ha hs ht
          subst token
          subst next'
          obtain ⟨rest,hcut,htrace⟩ := ih next hr tokens hrest (by simpa using hlen)
          exact ⟨rest,by simpa [List.replicate_succ] using congrArg (none :: ·) hcut,htrace⟩

theorem lift_trace (xs : List (Option Bool)) (a b : NDPrimitiveDispatcher.Program.Cfg (machine w))
    (h : NDPrimitiveDispatcher.Runs.Trace (machine w) xs a b) : Trace w xs (lift w a) (lift w b) := by
  induction xs generalizing a with
  | nil => exact h ▸ rfl
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := h
      exact ⟨lift w next,by rw [native_step,hs]; rfl,ih next hr⟩
theorem reflect_trace (xs : List (Option Bool)) (a : NDPrimitiveDispatcher.Program.Cfg (machine w)) (finalCfg : Cfg w)
    (h : Trace w xs (lift w a) finalCfg) :
    ∃ b, NDPrimitiveDispatcher.Runs.Trace (machine w) xs a b ∧ lift w b = finalCfg := by
  induction xs generalizing a with
  | nil => exact ⟨a,rfl,h⟩
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := h
      rw [native_step] at hs
      cases ht : Native.step (machine w) token a with
      | none => simp only [ht,Option.map_none,Option.bind_none] at hs; cases hs
      | some b =>
          have he : lift w b = next := Option.some.inj (by simpa [ht] using hs)
          obtain ⟨c,hc,hend⟩ := ih b (he.symm ▸ hr)
          exact ⟨c,⟨b,ht,hc⟩,hend⟩

def projection : PointedMap (Symbol w) (Native.Alphabet (machine w)) :=
  ⟨fun a => match a with | .native b => b | _ => default,rfl⟩
theorem map_cancel (T : Tape (Native.Alphabet (machine w))) :
    (T.map (inclusion w)).map (projection w) = T := by
  have hl : (T.left.map (inclusion w)).map (projection w) = T.left :=
    ListBlank.ext (fun n => by rw [ListBlank.nth_map,ListBlank.nth_map]; rfl)
  have hr : (T.right.map (inclusion w)).map (projection w) = T.right :=
    ListBlank.ext (fun n => by rw [ListBlank.nth_map,ListBlank.nth_map]; rfl)
  cases T
  simp only [Tape.map] at hl hr ⊢
  rw [hl,hr]
  rfl
theorem lift_injective : Function.Injective (lift w) := by
  intro a b h
  have hq : a.q = b.q := Sum.inr.inj (congrArg TM0.Cfg.q h)
  have ht := congrArg (fun c : Cfg w => c.Tape.map (projection w)) h
  simp only [lift,map_cancel] at ht
  cases a; cases b; cases hq; cases ht; rfl

def clock : Polynomial ℕ := Execution.polynomial+NDPrimitiveDispatcher.Paths.clock w
theorem clock_eval (word : List Bool) : (clock w).eval word.length =
    Execution.steps word.length+(NDPrimitiveDispatcher.Paths.clock w).eval word.length := by
  simp [clock,Execution.polynomial_eval]
theorem split_prepare (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Trace w xs (initial w word) finalCfg) (hend : finalCfg.q.isLeft = false) :
    ∃ rest, xs = List.replicate (Execution.steps word.length) none++rest ∧
      Trace w rest (lift w (NDPrimitiveDispatcher.Paths.initial w word)) finalCfg := by
  obtain ⟨before,hfront,hpre,hstep⟩ := Execution.prepare_before w word
  rcases before_match w _ _ before finalCfg hpre hfront xs h with ⟨hlen,hleft⟩ | ⟨rest,hcut,hr⟩
  · rw [hend] at hleft; cases hleft
  · cases rest with
    | nil => change before = finalCfg at hr; have he := congrArg (fun c : Cfg w => c.q.isLeft) hr; rw [hfront,hend] at he; cases he
    | cons token tokens =>
        obtain ⟨next,hs,ht⟩ := hr
        obtain ⟨he,hn⟩ := front_edge w token before _ next hfront hstep hs
        subst token
        subst next
        refine ⟨tokens,?_,ht⟩
        have hlen : Execution.steps word.length-1+1 = Execution.steps word.length := by
          unfold Execution.steps
          omega
        have hrep : List.replicate (Execution.steps word.length-1) (none : Option Bool)++[none] =
            List.replicate (Execution.steps word.length) none := by
          change List.replicate (Execution.steps word.length-1) (none : Option Bool)++
            List.replicate 1 none = List.replicate (Execution.steps word.length) none
          rw [← List.replicate_add,hlen]
        calc
          xs = List.replicate (Execution.steps word.length-1) none++(none::tokens) := hcut
          _ = (List.replicate (Execution.steps word.length-1) none++[none])++tokens := by simp [List.append_assoc]
          _ = List.replicate (Execution.steps word.length) none++tokens := by rw [hrep]

theorem prefix_time (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Trace w xs (initial w word) finalCfg) : xs.length ≤ (clock w).eval word.length := by
  obtain ⟨before,hfront,hpre,hstep⟩ := Execution.prepare_before w word
  rcases before_match w _ _ before finalCfg hpre hfront xs h with ⟨hlen,hleft⟩ | ⟨rest,hcut,hr⟩
  · rw [clock_eval]; omega
  · cases rest with
    | nil => rw [hcut,List.length_append,List.length_replicate,List.length_nil,clock_eval]; omega
    | cons token tokens =>
        obtain ⟨next,hs,ht⟩ := hr
        obtain ⟨he,hn⟩ := front_edge w token before _ next hfront hstep hs
        subst token
        subst next
        obtain ⟨native,hnative,heq⟩ := reflect_trace w tokens _ finalCfg ht
        have hb := NDPrimitiveDispatcher.Paths.prefix_time w word tokens native hnative
        rw [hcut,List.length_append,List.length_replicate,List.length_cons,clock_eval]
        unfold Execution.steps
        omega

/-- No raw-input pre needs a supplied halt result. Its actual frontend
continuation and the installed dispatcher's all-raw continuation are produced
internally. The endpoint is the old real halt, not held zero-step padding. -/
theorem prefix_completion (word : List Bool) (xs : List (Option Bool)) (finalCfg : Cfg w)
    (h : Trace w xs (initial w word) finalCfg) :
    ∃ rest c, Trace w rest finalCfg (lift w (NDPrimitiveDispatcher.Program.embed (machine w) c)) ∧
      NDPrimitiveDispatcher.Program.Halted (machine w) (NDPrimitiveDispatcher.Program.embed (machine w) c) ∧
      (xs++rest).length ≤ (clock w).eval word.length := by
  obtain ⟨before,hfront,hpre,hstep⟩ := Execution.prepare_before w word
  have handoff : Trace w [none] before (lift w (NDPrimitiveDispatcher.Paths.initial w word)) :=
    ⟨_,hstep,rfl⟩
  have finish_from_before : ∃ rest c,
      Trace w rest before (lift w (NDPrimitiveDispatcher.Program.embed (machine w) c)) ∧
      NDPrimitiveDispatcher.Program.Halted (machine w) (NDPrimitiveDispatcher.Program.embed (machine w) c) := by
    obtain ⟨rest,c,hr,hh,hbound⟩ := NDPrimitiveDispatcher.Paths.prefix_completion w word [] _ rfl
    exact ⟨[none]++rest,c,append w _ _ _ _ _ handoff (lift_trace w _ _ _ hr),hh⟩
  rcases before_match w _ _ before finalCfg hpre hfront xs h with ⟨hlen,hleft⟩ | ⟨remaining,hcut,hr⟩
  · obtain ⟨pending,hpending,htrace⟩ := before_completion w _ _ before finalCfg hpre hfront xs h hlen
    obtain ⟨tail,c,htail,hh⟩ := finish_from_before
    have hc := append w pending tail finalCfg before _ htrace htail
    exact ⟨pending++tail,c,hc,hh,prefix_time w word _ _ (append w xs _ _ finalCfg _ h hc)⟩
  · cases remaining with
    | nil =>
        change before = finalCfg at hr
        obtain ⟨tail,c,htail,hh⟩ := finish_from_before
        have hc : Trace w tail finalCfg _ := hr ▸ htail
        exact ⟨tail,c,hc,hh,prefix_time w word _ _ (append w xs _ _ finalCfg _ h hc)⟩
    | cons token tokens =>
        obtain ⟨next,hs,ht⟩ := hr
        obtain ⟨he,hn⟩ := front_edge w token before _ next hfront hstep hs
        subst token
        subst next
        obtain ⟨native,hnative,heq⟩ := reflect_trace w tokens _ finalCfg ht
        obtain ⟨tail,c,htail,hh,hbound⟩ := NDPrimitiveDispatcher.Paths.prefix_completion w word tokens native hnative
        have hc : Trace w tail finalCfg _ := heq ▸ lift_trace w tail native _ htail
        exact ⟨tail,c,hc,hh,prefix_time w word _ _ (append w xs _ _ finalCfg _ h hc)⟩

theorem lift_halted (c : NDPrimitiveDispatcher.Program.Cfg (machine w))
    (hc : NDPrimitiveDispatcher.Program.Halted (machine w) c) (token : Option Bool) :
    step w token (lift w c) = none := by
  rw [native_step,NDPrimitiveDispatcher.Program.halt_no_edge (machine w) c hc token]
  rfl

abbrev Path (word : List Bool) := {xs : List (Option Bool) // ∃ c : TapeSimulation.FiniteCfg (machine w),
  TapeSimulation.Encoded (machine w) (haltList (machine w).core [true]) (TapeSimulation.forget (machine w) c) ∧
  Trace w xs (initial w word) (lift w (NDPrimitiveDispatcher.Program.embed (machine w) c))}
def forward (word : List Bool) (p : NDPrimitiveDispatcher.Paths.Path w word) : Path w word :=
  ⟨List.replicate (Execution.steps word.length) none++p.val,by
    obtain ⟨c,hc,hr⟩ := p.property
    exact ⟨c,hc,append w _ _ _ _ _ (rows_trace w _ _ _ (Execution.prepare w word)) (lift_trace w p.val _ _ hr)⟩⟩
theorem forward_guesses (word : List Bool) (p : NDPrimitiveDispatcher.Paths.Path w word) :
    (forward w word p).val.filterMap id = p.val.filterMap id := by
  simp [forward,List.filterMap_append]
theorem backward_exists (word : List Bool) (p : Path w word) :
    ∃ q : NDPrimitiveDispatcher.Paths.Path w word,
      p.val = List.replicate (Execution.steps word.length) none++q.val := by
  obtain ⟨c,hc,hr⟩ := p.property
  obtain ⟨rest,hcut,hrest⟩ := split_prepare w word p.val _ hr rfl
  obtain ⟨native,hnative,he⟩ := reflect_trace w rest _ _ hrest
  have hend := lift_injective w he
  exact ⟨⟨rest,c,hc,hend ▸ hnative⟩,hcut⟩
def backward (word : List Bool) (p : Path w word) : NDPrimitiveDispatcher.Paths.Path w word :=
  Classical.choose (backward_exists w word p)
def pathsEquiv (word : List Bool) : NDPrimitiveDispatcher.Paths.Path w word ≃ Path w word where
  toFun := forward w word
  invFun := backward w word
  left_inv p := by
    apply Subtype.ext
    have hc := Classical.choose_spec (backward_exists w word (forward w word p))
    exact List.append_cancel_left hc.symm
  right_inv p := by
    apply Subtype.ext
    exact (Classical.choose_spec (backward_exists w word p)).symm
noncomputable instance (word : List Bool) : Fintype (Path w word) :=
  Fintype.ofEquiv (NDPrimitiveDispatcher.Paths.Path w word) (pathsEquiv w word)
def count (word : List Bool) : ℕ := Fintype.card (Path w word)
theorem raw_count (word : List Bool) : count w word = NDPrimitiveDispatcher.Paths.count w word :=
  Fintype.card_congr (pathsEquiv w word).symm
def originalPathsEquiv (a : α) : ConventionalSharpPSource.AcceptedWitness w a ≃ Path w (TotalRawSource.encodedInput w a) :=
  (NDPrimitiveDispatcher.Paths.originalPathsEquiv w a).trans (pathsEquiv w _)
theorem encoded_count (a : α) : count w (TotalRawSource.encodedInput w a) = f a :=
  (raw_count w _).trans (NDPrimitiveDispatcher.Paths.encoded_count w a)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Composition
