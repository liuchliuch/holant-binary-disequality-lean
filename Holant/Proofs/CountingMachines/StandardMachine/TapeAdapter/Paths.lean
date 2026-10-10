import Holant.Proofs.CountingMachines.StandardMachine.TapeAdapter.Basic

set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
open Turing

namespace Model
variable {Γ Q Δ : Type} (m : Model Γ Q)

/-- Polynomial source membership on a typed input subalphabet. This does not
claim termination on arbitrary words over the larger work alphabet. -/
def PolyTimeOn (input : Δ → Γ) (clock : Polynomial ℕ) : Prop :=
  ∀ (word : List Δ) (tokens : List (Option Bool)) (finish : Config Γ Q),
    m.PhysicalTrace tokens (m.initialConfig (word.map input)) finish →
      tokens.length ≤ clock.eval word.length

/-- Typed nonblank letters give physically distinct initial configurations,
including the empty word and words whose final letter represents Boolean false. -/
theorem initialConfig_map_injective (input : Δ → Γ) (hinj : Function.Injective input)
    (hn : ∀ a, input a ≠ m.blank) :
    Function.Injective (fun word : List Δ => m.initialConfig (word.map input)) := by
  intro xs ys h
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b ys =>
          have he : m.blank = input b := congrArg Config.head h
          exact False.elim (hn b he.symm)
  | cons a xs =>
      cases ys with
      | nil =>
          have he : input a = m.blank := congrArg Config.head h
          exact False.elim (hn a he)
      | cons b ys =>
          have he : input a = input b := congrArg Config.head h
          have ht : xs.map input = ys.map input := congrArg Config.right h
          exact congrArg₂ List.cons (hinj he) (List.map_injective_iff.mpr hinj ht)

theorem physicalTrace_append (xs ys : List (Option Bool)) (a b c : Config Γ Q)
    (hxs : m.PhysicalTrace xs a b) (hys : m.PhysicalTrace ys b c) :
    m.PhysicalTrace (xs ++ ys) a c := by
  induction xs generalizing a with
  | nil => subst b; exact hys
  | cons token rest ih =>
      obtain ⟨next, hs, ht⟩ := hxs
      exact ⟨next, hs, ih next ht⟩

/-- A running control always has a real next row. Select the false branch
when a choice is required; this is a literal finite-control decision. -/
theorem running_step (c : Config Γ Q) (hc : m.verdict c.control = none) :
    m.physicalStep (if m.choose c.control then some false else none) c =
      some (m.execute false c) := by
  cases hb : m.choose c.control <;> simp [physicalStep,step,hc,hb]

/-- Typed prefix bounds imply stopping at the deadline because every running
control has an outgoing row. This assertion does not quantify over untyped
work-alphabet input words. -/
theorem polyTimeOn_deadline (input : Δ → Γ) (clock : Polynomial ℕ)
    (htime : m.PolyTimeOn input clock) (word : List Δ) (tokens : List (Option Bool))
    (finish : Config Γ Q)
    (ht : m.PhysicalTrace tokens (m.initialConfig (word.map input)) finish)
    (hlen : tokens.length = clock.eval word.length) :
    (m.verdict finish.control).isSome = true := by
  cases hv : m.verdict finish.control with
  | some b => rfl
  | none =>
      let token := if m.choose finish.control then some false else none
      have hs : m.PhysicalTrace [token] finish (m.execute false finish) :=
        ⟨_,m.running_step finish hv,rfl⟩
      have hb := htime word (tokens ++ [token]) (m.execute false finish)
        (m.physicalTrace_append _ _ _ _ _ ht hs)
      simp only [List.length_append,List.length_singleton] at hb
      omega

/-- Every real prefix can be physically completed to a stopped control.
No guessed stopping time or extra nondeterministic bits are supplied. -/
theorem polyTimeOn_completion (input : Δ → Γ) (clock : Polynomial ℕ)
    (htime : m.PolyTimeOn input clock) (word : List Δ) (tokens : List (Option Bool))
    (finish : Config Γ Q)
    (ht : m.PhysicalTrace tokens (m.initialConfig (word.map input)) finish) :
    ∃ rest endCfg, m.PhysicalTrace rest finish endCfg ∧
      (m.verdict endCfg.control).isSome = true ∧
      (tokens ++ rest).length ≤ clock.eval word.length := by
  have complete (remaining : ℕ) :
      ∀ (tokens : List (Option Bool)) (finish : Config Γ Q),
        m.PhysicalTrace tokens (m.initialConfig (word.map input)) finish →
        tokens.length + remaining = clock.eval word.length →
        ∃ rest endCfg, m.PhysicalTrace rest finish endCfg ∧
          (m.verdict endCfg.control).isSome = true ∧
          (tokens ++ rest).length ≤ clock.eval word.length := by
    induction remaining with
    | zero =>
        intro tokens finish ht he
        exact ⟨[],finish,rfl,m.polyTimeOn_deadline input clock htime word tokens finish ht
          (by simpa using he),by simpa using htime word tokens finish ht⟩
    | succ remaining ih =>
        intro tokens finish ht he
        cases hv : m.verdict finish.control with
        | some b => exact ⟨[],finish,rfl,by simp [hv],by simpa using htime word tokens finish ht⟩
        | none =>
            let token := if m.choose finish.control then some false else none
            have hs : m.PhysicalTrace [token] finish (m.execute false finish) :=
              ⟨_,m.running_step finish hv,rfl⟩
            have hnext := m.physicalTrace_append _ _ _ _ _ ht hs
            obtain ⟨rest,endCfg,hr,hstop,hb⟩ := ih (tokens ++ [token]) (m.execute false finish)
              hnext (by simp only [List.length_append,List.length_singleton]; omega)
            refine ⟨token :: rest,endCfg,⟨_,m.running_step finish hv,hr⟩,?_,?_⟩
            · exact hstop
            · simpa [List.append_assoc] using hb
  apply complete (clock.eval word.length - tokens.length) tokens finish ht
  exact Nat.add_sub_of_le (htime word tokens finish ht)

/-- Every physical accepting path receives exactly one forced padding suffix. -/
def allPhysicalPathEquivOn (input : Δ → Γ) (clock : Polynomial ℕ)
    (htime : m.PolyTimeOn input clock) (word : List Δ) :
    m.PhysicalPath (word.map input) ≃
      m.AcceptedPath (clock.eval word.length) (word.map input) :=
  (show m.PhysicalPath (word.map input) ≃
      m.ShortPhysicalPath (clock.eval word.length) (word.map input) from
    { toFun := fun p => ⟨p.val, by
        obtain ⟨finish, ha, ht⟩ := p.property
        exact ⟨htime word p.val finish ht, finish, ha, ht⟩⟩
      invFun := fun p => ⟨p.val, p.property.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }).trans
    (m.physicalPathEquiv (clock.eval word.length) (word.map input))
end Model

namespace TapeAdapter.Primitive
variable {Γ Q Δ : Type} [Inhabited Γ] [Inhabited Q] (p : Primitive Γ Q)

theorem sink_trace (tokens : List (Option Bool)) (c d : Config Γ (Option Q))
    (hc : view c = none) (h : p.model.PhysicalTrace tokens c d) : tokens = [] ∧ c = d := by
  cases tokens with
  | nil => exact ⟨rfl,h⟩
  | cons token rest =>
      obtain ⟨next,hs,hr⟩ := h
      rw [p.sink_stops token c hc] at hs
      cases hs

/-- Reflection uses equality of the quotient tapes, and retains the complete
edge-label word. Equal successor configurations never identify branch labels. -/
theorem trace_reflect (tokens : List (Option Bool)) (c d : Config Γ (Option Q))
    (a b : TM0.Cfg Γ Q) (hc : view c = some a) (hd : view d = some b)
    (h : p.model.PhysicalTrace tokens c d) : p.Trace tokens a b := by
  induction tokens generalizing c a with
  | nil =>
      change c = d at h
      subst d
      exact Option.some.inj (hc.symm.trans hd)
  | cons token rest ih =>
      obtain ⟨next,hs,hr⟩ := h
      cases hn : view next with
      | none =>
          obtain ⟨_,he⟩ := p.sink_trace rest next d hn hr
          rw [he,hd] at hn
          cases hn
      | some middle =>
          have hp := p.physicalStep_view token c a hc
          rw [hs] at hp
          have hstep : p.step token a = some middle := by simpa [hn] using hp.symm
          exact ⟨middle,hstep,ih next middle hn hr⟩

def pathEquiv (word : List Γ) : p.Path word ≃ p.model.PhysicalPath word where
  toFun := fun path => ⟨path.val, by
    obtain ⟨finish,ha,ht⟩ := path.property
    obtain ⟨d,hd,hv⟩ := p.trace_lift path.val _ _ finish (p.view_initial word) ht
    exact ⟨d,(p.accepts_view d).mpr ⟨finish,hv,ha⟩,hd⟩⟩
  invFun := fun path => ⟨path.val, by
    obtain ⟨finish,ha,ht⟩ := path.property
    obtain ⟨b,hb,haccept⟩ := (p.accepts_view finish).mp ha
    exact ⟨b,haccept,p.trace_reflect path.val _ finish _ b (p.view_initial word) hb ht⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

@[simp] theorem pathEquiv_labels (word : List Γ) (path : p.Path word) :
    (p.pathEquiv word path).val = path.val := rfl

@[simp] theorem pathEquiv_symm_labels (word : List Γ) (path : p.model.PhysicalPath word) :
    ((p.pathEquiv word).symm path).val = path.val := rfl

/-- Every zipper pre contains a genuine source pre and at most one
additional row, the write entering the new rejecting control. -/
theorem prefix_projection (tokens : List (Option Bool)) (c d : Config Γ (Option Q))
    (a : TM0.Cfg Γ Q) (hc : view c = some a)
    (h : p.model.PhysicalTrace tokens c d) :
    ∃ pre b, p.Trace pre a b ∧ tokens.length ≤ pre.length + 1 := by
  induction tokens generalizing c a with
  | nil => exact ⟨[],a,rfl,by simp⟩
  | cons token rest ih =>
      obtain ⟨next,hs,hr⟩ := h
      cases hn : view next with
      | none =>
          obtain ⟨hz,_⟩ := p.sink_trace rest next d hn hr
          exact ⟨[],a,rfl,by simp [hz]⟩
      | some middle =>
          have hp := p.physicalStep_view token c a hc
          rw [hs] at hp
          have hstep : p.step token a = some middle := by simpa [hn] using hp.symm
          obtain ⟨pre,b,hpre,hbound⟩ := ih next middle hn hr
          exact ⟨token :: pre,b,⟨middle,hstep,hpre⟩,by simp only [List.length_cons]; omega⟩

/-- Legitimate source data only for words of the declared input alphabet. -/
def PolyTimeOn (input : Δ → Γ) (clock : Polynomial ℕ) : Prop :=
  ∀ (word : List Δ) (tokens : List (Option Bool)) (finish : TM0.Cfg Γ Q),
    p.Trace tokens (p.initial (word.map input)) finish →
      tokens.length ≤ clock.eval word.length

theorem model_polyTimeOn (input : Δ → Γ) (clock : Polynomial ℕ)
    (htime : p.PolyTimeOn input clock) :
    p.model.PolyTimeOn input (clock + Polynomial.C 1) := by
  intro word tokens finish ht
  obtain ⟨pre,b,hpre,hbound⟩ :=
    p.prefix_projection tokens _ finish _ (p.view_initial (word.map input)) ht
  have hp := htime word pre b hpre
  simpa using hbound.trans (Nat.add_le_add_right hp 1)

noncomputable def paddedPathEquiv (input : Δ → Γ) (clock : Polynomial ℕ)
    (htime : p.PolyTimeOn input clock) (word : List Δ) :
    p.Path (word.map input) ≃
      p.model.AcceptedPath ((clock + Polynomial.C 1).eval word.length) (word.map input) :=
  (p.pathEquiv _).trans
    (p.model.allPhysicalPathEquivOn input _ (p.model_polyTimeOn input clock htime) word)

/-- The complete original word is followed by a uniquely determined suffix.
In particular, choices are never appended after physical stopping. -/
@[simp] theorem paddedPathEquiv_labels (input : Δ → Γ) (clock : Polynomial ℕ)
    (htime : p.PolyTimeOn input clock) (word : List Δ) (path : p.Path (word.map input)) :
    (p.paddedPathEquiv input clock htime word path).val = path.val ++
      List.replicate ((clock + Polynomial.C 1).eval word.length - path.val.length) none := rfl

end TapeAdapter.Primitive
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
