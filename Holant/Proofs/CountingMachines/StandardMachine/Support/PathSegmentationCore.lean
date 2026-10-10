import Holant.Proofs.CountingMachines.StandardMachine.Support.TapeSimulationCore

set_option backward.isDefEq.respectTransparency false
/-!
Adapted reference proof. See the task validation reports. Reverse segmentation of actual, unsegmented finite TM1
instruction paths of the SAME TapeSimulation programme. The normal/go/ret
marker is already in its finite label table; no new dispatcher is installed.
Every accepted path is a literal finiteStep trace ending at the encoded clean
true halt. No arbitrary instruction word or free segmentation law is accepted.

The observer records a token only before an actual normal-table row. Internal
go/ret rows are proved deterministic None edges. Real halt has no successor;
held source padding is generated afterwards and has zero physical moves.
This file proves path/count transport, not a new time bound or TM0 dispatcher.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.PathSegmentation
open Turing Computability Holant.Complexity StateTransition Relation
namespace Tape
export TapeSimulation
  (FiniteCfg finiteStep finiteInternalStep forget boundary Encoded InstructionTrace FiniteTrace
    finiteInitial programme)
end Tape

variable (m : BinaryMachine)
abbrev Cfg := Tape.FiniteCfg m

def normal (a : Cfg m) : Bool :=
  match a.l with
  | some l => match l.val with
    | .normal _ => true
    | _ => false
  | none => false

def atBoundary (a : Cfg m) : Prop := Tape.boundary m (Tape.forget m a)

instance boundaryDecidable (a : Cfg m) : Decidable (atBoundary m a) := by
  unfold atBoundary TapeSimulation.boundary TapeSimulation.forget
  cases a.l with
  | none => exact isTrue trivial
  | some l =>
      cases hv : l.val with
      | normal _ => exact isTrue (by simp [hv])
      | go _ _ _ => exact isFalse (by simp [hv])
      | ret _ => exact isFalse (by simp [hv])

theorem halt_boundary (a : Cfg m) (h : a.l = none) : atBoundary m a := by
  simp [atBoundary,TapeSimulation.boundary,TapeSimulation.forget,h]

theorem halt_no_edge (a : Cfg m) (h : a.l = none) (token : Option Bool) :
    Tape.finiteStep m token a = none := by simp [TapeSimulation.finiteStep,h]

theorem normal_of_boundary_edge (token : Option Bool) (a b : Cfg m)
    (ha : atBoundary m a) (h : Tape.finiteStep m token a = some b) : normal m a = true := by
  cases hl : a.l with
  | none => simp [TapeSimulation.finiteStep,hl] at h
  | some l =>
      cases hv : l.val with
      | normal label => simp [normal,hl,hv]
      | go k action q => simp [atBoundary,TapeSimulation.boundary,TapeSimulation.forget,hl,hv] at ha
      | ret q => simp [atBoundary,TapeSimulation.boundary,TapeSimulation.forget,hl,hv] at ha

/-- Reverse direction of the installed internal row law. A genuine interior
edge must use None and is exactly the finiteInternalStep edge. -/
theorem internal_edge (token : Option Bool) (a b : Cfg m)
    (ha : ¬ atBoundary m a) (h : Tape.finiteStep m token a = some b) :
    token = none ∧ Tape.finiteInternalStep m a = some b ∧ normal m a = false := by
  cases hl : a.l with
  | none => exact False.elim (ha (halt_boundary m a hl))
  | some l =>
      cases hv : l.val with
      | normal label =>
          exact False.elim (ha (by simp [atBoundary,TapeSimulation.boundary,TapeSimulation.forget,hl,hv]))
      | go k action q =>
          cases token with
          | none => exact ⟨rfl,by simpa only [TapeSimulation.finiteInternalStep,hl,hv] using h,
              by simp [normal,hl,hv]⟩
          | some bit => simp [TapeSimulation.finiteStep,TapeSimulation.programme,TapeSimulation.split,hl,hv] at h
      | ret q =>
          cases token with
          | none => exact ⟨rfl,by simpa only [TapeSimulation.finiteInternalStep,hl,hv] using h,
              by simp [normal,hl,hv]⟩
          | some bit => simp [TapeSimulation.finiteStep,TapeSimulation.programme,TapeSimulation.split,hl,hv] at h

def Interior : ℕ → Cfg m → Cfg m → Prop
  | 0,a,b => a = b
  | n+1,a,b => ∃ next, Tape.finiteInternalStep m a = some next ∧ Interior n next b

theorem interior_reaches (n : ℕ) (a b : Cfg m) (h : Interior m n a b) :
    Reaches (Tape.finiteInternalStep m) a b := by
  induction n generalizing a with
  | zero => subst a; exact ReflTransGen.refl
  | succ n ih =>
      obtain ⟨next,hs,hr⟩ := h
      exact (ih next hr).head hs

theorem interior_stops (a : Cfg m) (ha : atBoundary m a) : Tape.finiteInternalStep m a = none := by
  cases hl : a.l with
  | none => simp [TapeSimulation.finiteInternalStep,hl]
  | some l =>
      cases hv : l.val with
      | normal label => simp [TapeSimulation.finiteInternalStep,hl,hv]
      | go k action q => simp [atBoundary,TapeSimulation.boundary,TapeSimulation.forget,hl,hv] at ha
      | ret q => simp [atBoundary,TapeSimulation.boundary,TapeSimulation.forget,hl,hv] at ha

/-- The first normal/halt return fixes both its physical number of rows and
its endpoint. No unused interior rows can be added to a legitimate interval. -/
theorem interior_unique (n k : ℕ) (a b c : Cfg m)
    (hb : Interior m n a b) (hc : Interior m k a c)
    (hbh : atBoundary m b) (hch : atBoundary m c) : n = k ∧ b = c := by
  induction n generalizing k a with
  | zero =>
      change a = b at hb
      subst a
      cases k with
      | zero => exact ⟨rfl,hc⟩
      | succ k =>
          obtain ⟨next,hs,hr⟩ := hc
          rw [interior_stops m b hbh] at hs
          cases hs
  | succ n ih =>
      obtain ⟨next,hs,hr⟩ := hb
      cases k with
      | zero =>
          change a = c at hc
          subst a
          rw [interior_stops m c hch] at hs
          cases hs
      | succ k =>
          obtain ⟨other,ht,hr'⟩ := hc
          have he : next = other := Option.some.inj (hs.symm.trans ht)
          subst other
          obtain ⟨hlen,hend⟩ := ih k next hr hr'
          exact ⟨congrArg Nat.succ hlen,hend⟩

/-- Stop at the FIRST boundary. Each consumed prefix row is an actual
internal edge, so it cannot cross a normal row or introduce a branch bit. -/
theorem first_boundary (instructions : List (Option Bool)) (a b : Cfg m)
    (h : Tape.InstructionTrace m instructions a b) (hb : atBoundary m b) :
    ∃ n : ℕ, ∃ rest : List (Option Bool), ∃ mid : Cfg m,
      instructions = List.replicate n none++rest ∧ Interior m n a mid ∧
      atBoundary m mid ∧ Tape.InstructionTrace m rest mid b ∧ rest.length ≤ instructions.length := by
  induction instructions generalizing a with
  | nil =>
      change a = b at h
      subst a
      exact ⟨0,[],b,rfl,rfl,hb,rfl,le_rfl⟩
  | cons token instructions ih =>
      by_cases ha : atBoundary m a
      · exact ⟨0,token::instructions,a,rfl,rfl,ha,h,le_rfl⟩
      · obtain ⟨next,hs,hr⟩ := h
        obtain ⟨ht,hstep,hnot⟩ := internal_edge m token a next ha hs
        subst token
        obtain ⟨n,rest,mid,hcut,hint,hmid,hrest,hlen⟩ := ih next hr
        refine ⟨n+1,rest,mid,?_,⟨next,hstep,hint⟩,hmid,hrest,?_⟩
        · simp only [List.replicate_succ,List.cons_append,hcut]
        · exact hlen.trans (by simp)

/-- Mathematical path observer of the existing finite syntax. Its option
result rejects any illegal edge; it is not a runtime callback for the source. -/
def segment : List (Option Bool) → Cfg m → Option (List (Option Bool) × Cfg m)
  | [],a => some ([],a)
  | token::tokens,a => (Tape.finiteStep m token a).bind fun next =>
      (segment tokens next).map fun result =>
        (if normal m a then token::result.1 else result.1,result.2)

theorem interior_segment (n : ℕ) (a mid : Cfg m) (h : Interior m n a mid)
    (rest : List (Option Bool)) :
    segment m (List.replicate n none++rest) a = segment m rest mid := by
  induction n generalizing a with
  | zero => subst a; rfl
  | succ n ih =>
      obtain ⟨next,hs,hr⟩ := h
      have hedges := TapeSimulation.finite_internal_no_choice m a next hs
      have hn : normal m a = false := by
        cases hl : a.l with
        | none => simp [TapeSimulation.finiteInternalStep,hl] at hs
        | some l => cases hv : l.val <;> simp_all [normal,TapeSimulation.finiteInternalStep]
      simp only [List.replicate_succ,List.cons_append,segment,hedges.1,Option.bind_some,hn,
        Bool.false_eq_true,if_false]
      cases hseg : segment m (List.replicate n none++rest) next <;>
        simpa only [hseg,Option.map_none,Option.map_some] using ih next hr

/-- A real boundary macro has a nonempty physical first row. Unlike the old
held trace it has no padding constructor and hence cannot advance after halt. -/
def RealMacro (token : Option Bool) (a b : Cfg m) : Prop :=
  ∃ first, Tape.finiteStep m token a = some first ∧
    Reaches (Tape.finiteInternalStep m) first b ∧ atBoundary m b

def RealTrace : List (Option Bool) → Cfg m → Cfg m → Prop
  | [],a,b => a = b
  | token::tokens,a,b => ∃ next, RealMacro m token a next ∧ RealTrace tokens next b

theorem real_trace_old (tokens : List (Option Bool)) (a b : Cfg m)
    (h : RealTrace m tokens a b) : Tape.FiniteTrace m tokens a b := by
  induction tokens generalizing a with
  | nil => exact h
  | cons token tokens ih =>
      obtain ⟨mid,⟨first,hf,hr,hb⟩,hrest⟩ := h
      exact ⟨mid,TapeSimulation.FiniteMacro.real first hf hr hb,ih mid hrest⟩

/-- Actual reverse segmentation. The strict decrease is the remaining
physical instruction length, not a caller-provided horizon. -/
theorem segment_correct (instructions : List (Option Bool)) (a b : Cfg m)
    (ha : atBoundary m a) (hb : atBoundary m b)
    (h : Tape.InstructionTrace m instructions a b) :
    ∃ tokens : List (Option Bool), segment m instructions a = some (tokens,b) ∧
      RealTrace m tokens a b ∧ tokens.filterMap id = instructions.filterMap id := by
  induction hlen : instructions.length using Nat.strong_induction_on generalizing instructions a with
  | h length ih =>
      cases instructions with
      | nil =>
          change a = b at h
          subst a
          exact ⟨[],rfl,rfl,rfl⟩
      | cons token instructions =>
          obtain ⟨first,hfirst,hrest⟩ := h
          have hnormal := normal_of_boundary_edge m token a first ha hfirst
          obtain ⟨n,rest,mid,hcut,hint,hmid,hr,hrlen⟩ := first_boundary m instructions first b hrest hb
          have hlt : rest.length < length := by simp only [List.length_cons] at hlen; omega
          obtain ⟨tokens,hseg,hreal,hlog⟩ :=
            ih rest.length hlt (instructions := rest) (a := mid) hmid hr rfl
          refine ⟨token::tokens,?_,⟨mid,⟨first,hfirst,interior_reaches m n first mid hint,hmid⟩,hreal⟩,?_⟩
          · simp only [segment,hfirst,Option.bind_some,hnormal,ite_true]
            rw [hcut,interior_segment m n first mid hint rest,hseg]
            rfl
          · rw [hcut]
            cases token <;> simpa using hlog

theorem segment_unique (instructions : List (Option Bool)) (a b c : Cfg m)
    (left right : List (Option Bool))
    (hl : segment m instructions a = some (left,b))
    (hr : segment m instructions a = some (right,c)) : left = right ∧ b = c :=
  Prod.mk.inj (Option.some.inj (hl.symm.trans hr))

def ActiveTrace : List (Option Bool) → m.Config → m.Config → Prop
  | [],a,b => a = b
  | token::tokens,a,b => a.l.isSome = true ∧ ∃ next, m.step token a = some next ∧ ActiveTrace tokens next b

theorem active_old (tokens : List (Option Bool)) (a b : m.Config)
    (h : ActiveTrace m tokens a b) : m.TraceValid tokens a b := by
  induction tokens generalizing a with
  | nil => exact h
  | cons token tokens ih =>
      obtain ⟨_,next,hs,hr⟩ := h
      exact ⟨next,hs,ih next hr⟩

theorem real_reflects (tokens : List (Option Bool)) (c : m.Config) (a b : Cfg m)
    (he : Tape.Encoded m c (Tape.forget m a)) (h : RealTrace m tokens a b) :
    ∃ d : m.Config, ActiveTrace m tokens c d ∧ Tape.Encoded m d (Tape.forget m b) := by
  induction tokens generalizing c a with
  | nil => exact ⟨c,rfl,h ▸ he⟩
  | cons token tokens ih =>
      obtain ⟨mid,⟨first,hf,hr,hb⟩,hrest⟩ := h
      have hc : c.l.isSome = true := by
        cases hl : c.l with
        | some l => simp [hl]
        | none =>
            have hlabel := TapeSimulation.encoded_label m c _ he
            have hal : a.l = none := by
              cases ha : a.l with
              | none => rfl
              | some l => simp [TapeSimulation.forget,hl,ha] at hlabel
            simp [TapeSimulation.finiteStep,hal] at hf
      have hm := TapeSimulation.finite_macro_forget m token a mid
        (TapeSimulation.FiniteMacro.real first hf hr hb)
      obtain ⟨next,hs,hnext⟩ := TapeSimulation.reflects m token c _ _ he hm
      obtain ⟨d,hd,he'⟩ := ih next mid hnext hrest
      exact ⟨d,⟨hc,next,hs,hd⟩,he'⟩

theorem active_append (left right : List (Option Bool)) (a b : m.Config)
    (h : ActiveTrace m (left++right) a b) :
    ∃ mid, ActiveTrace m left a mid ∧ ActiveTrace m right mid b := by
  induction left generalizing a with
  | nil => exact ⟨a,rfl,h⟩
  | cons token tokens ih =>
      obtain ⟨hc,next,hs,hr⟩ := h
      obtain ⟨mid,hfirst,hrest⟩ := ih next hr
      exact ⟨mid,⟨hc,next,hs,hfirst⟩,hrest⟩

theorem finite_padding (n : ℕ) (a : Cfg m) (ha : a.l = none) :
    Tape.FiniteTrace m (List.replicate n none) a a := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨a,TapeSimulation.FiniteMacro.padding ha rfl rfl,ih⟩

theorem finite_append (left right : List (Option Bool)) (a mid b : Cfg m)
    (hl : Tape.FiniteTrace m left a mid) (hr : Tape.FiniteTrace m right mid b) :
    Tape.FiniteTrace m (left++right) a b := by
  induction left generalizing a with
  | nil => subst a; exact hr
  | cons token tokens ih =>
      obtain ⟨next,hs,ht⟩ := hl
      exact ⟨next,hs,ih next ht⟩

/-- Two possible actual rows at one configuration must consume the same
token whenever their remaining actual guess logs agree. -/
theorem edge_log (token other : Option Bool) (a b c : Cfg m)
    (left right : List Bool) (hb : Tape.finiteStep m token a = some b)
    (hc : Tape.finiteStep m other a = some c)
    (hlog : token.toList++left = other.toList++right) :
    token = other ∧ b = c ∧ left = right := by
  cases hl : a.l with
  | none => simp [TapeSimulation.finiteStep,hl] at hb
  | some l =>
      cases hs : (Tape.programme m).choose l with
      | false =>
          cases token with
          | some bit => simp [TapeSimulation.finiteStep,hl,hs] at hb
          | none =>
              cases other with
              | some bit => simp [TapeSimulation.finiteStep,hl,hs] at hc
              | none => exact ⟨rfl,Option.some.inj (hb.symm.trans hc),hlog⟩
      | true =>
          cases token with
          | none => simp [TapeSimulation.finiteStep,hl,hs] at hb
          | some bit =>
              cases other with
              | none => simp [TapeSimulation.finiteStep,hl,hs] at hc
              | some otherBit =>
                  have he : bit = otherBit ∧ left = right := List.cons.inj hlog
                  obtain ⟨rfl, htail⟩ := he
                  exact ⟨rfl,Option.some.inj (hb.symm.trans hc),htail⟩

/-- No multiplicity from interior row counts or unused choices: two actual
halting instruction paths with the same chronological guesses are identical. -/
theorem instruction_unique (instructions other : List (Option Bool)) (a b c : Cfg m)
    (hb : Tape.InstructionTrace m instructions a b) (hc : Tape.InstructionTrace m other a c)
    (hbh : b.l = none) (hch : c.l = none)
    (hlog : instructions.filterMap id = other.filterMap id) : instructions = other ∧ b = c := by
  induction instructions generalizing other a with
  | nil =>
      change a = b at hb
      subst a
      cases other with
      | nil => exact ⟨rfl,hc⟩
      | cons token tokens =>
          obtain ⟨next,hs,hr⟩ := hc
          rw [halt_no_edge m b hbh token] at hs
          cases hs
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := hb
      cases other with
      | nil =>
          change a = c at hc
          subst a
          rw [halt_no_edge m c hch token] at hs
          cases hs
      | cons otherToken otherTokens =>
          obtain ⟨otherNext,ht,hr'⟩ := hc
          have hlogs : token.toList++tokens.filterMap id = otherToken.toList++otherTokens.filterMap id := by
            cases token <;> cases otherToken <;> exact hlog
          obtain ⟨he,hnext,hrest⟩ := edge_log m token otherToken a next otherNext _ _ hs ht hlogs
          subst otherToken
          subst otherNext
          obtain ⟨hwords,hend⟩ := ih otherTokens next hr hr' hrest
          exact ⟨congrArg (token :: ·) hwords,hend⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.PathSegmentation
