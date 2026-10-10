import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.TapeAcceptance.Semantics

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Exact two-way simulation on the original labelled
edges. Token lists are unchanged; no observer branch consumes a choice bit.
Every source halt still has precisely the unique none padding edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (trueSymbol : m.core.Γ m.core.k₁)

theorem step_lift (token : Option Bool) (c : m.Config) :
    (machine m trueSymbol).step token (liftCfg m trueSymbol c) =
      (m.step token c).map (liftCfg m trueSymbol) := by
  have he (q : m.core.Stmt) : TM2.stepAux (statement m trueSymbol q)
      (c.var,none,false) c.stk = liftCfg m trueSymbol (TM2.stepAux q c.var c.stk) :=
    statement_stepAux m trueSymbol q c.var c.stk
  cases hl : c.l with
  | none =>
    cases token <;> simp [BinaryMachine.step,liftCfg,hl]
  | some l =>
    cases token with
    | none =>
      cases hs : m.split l <;>
        simp [BinaryMachine.step,machine,computer,liftCfg,hl,hs,he]
    | some b =>
      cases b <;> cases hs : m.split l <;>
        simp [BinaryMachine.step,machine,computer,liftCfg,hl,hs,he]

@[simp] theorem token_lift (log : List Bool) (c : m.Config) :
    (machine m trueSymbol).token (log,liftCfg m trueSymbol c) = m.token (log,c) := by
  cases hl : c.l <;> simp [BinaryMachine.token,liftCfg,machine,hl]

theorem advance_lift (log : List Bool) (c : m.Config) :
    (machine m trueSymbol).advance (log,liftCfg m trueSymbol c) =
      (m.advance (log,c)).map (fun s => (s.1,liftCfg m trueSymbol s.2)) := by
  have hlift : (liftCfg m trueSymbol c).l = c.l := rfl
  have hsplit : (machine m trueSymbol).split = m.split := rfl
  cases hl : c.l with
  | none => simp [BinaryMachine.advance,liftCfg,hl]
  | some l =>
    cases hs : m.split l with
    | false =>
      simp only [BinaryMachine.advance,hlift,hsplit,hl,hs,Bool.false_eq_true,ite_false]
      rw [step_lift]
      cases h : m.step none c <;> rfl
    | true =>
      cases log with
      | nil => simp [BinaryMachine.advance,liftCfg,machine,hl,hs]
      | cons b rest =>
        simp only [BinaryMachine.advance,hlift,hsplit,hl,hs,ite_true]
        rw [step_lift]
        cases h : m.step (some b) c <;> rfl

theorem run_lift (n : ℕ) (log : List Bool) (c : m.Config) :
    (machine m trueSymbol).run n (log,liftCfg m trueSymbol c) =
      (m.run n (log,c)).map (fun s => (s.1,liftCfg m trueSymbol s.2)) := by
  induction n generalizing log c with
  | zero => rfl
  | succ n ih =>
    rw [BinaryMachine.run,advance_lift,BinaryMachine.run]
    cases hs : m.advance (log,c) with
    | none => rfl
    | some next =>
      simpa only [Option.map_some,Option.bind_some] using ih next.1 next.2

theorem tokens_lift (n : ℕ) (log : List Bool) (c : m.Config) :
    (machine m trueSymbol).tokensOfRun n (log,liftCfg m trueSymbol c) =
      m.tokensOfRun n (log,c) := by
  induction n generalizing log c with
  | zero => rfl
  | succ n ih =>
    rw [BinaryMachine.tokensOfRun,BinaryMachine.tokensOfRun,token_lift,advance_lift]
    cases hs : m.advance (log,c) with
    | none => rfl
    | some next =>
      simpa only [Option.map_some,Option.getD_some] using congrArg
        (m.token (log,c) :: ·) (ih next.1 next.2)

/-- Recovery is proved from actual target step equations. Arbitrary target
states, accepting trajectories and simulation laws are not constructor data. -/
theorem trace_recover (tokens : List (Option Bool)) (c : m.Config)
    (d : (machine m trueSymbol).Config) :
    (machine m trueSymbol).TraceValid tokens (liftCfg m trueSymbol c) d ↔
      ∃ original, m.TraceValid tokens c original ∧ d = liftCfg m trueSymbol original := by
  induction tokens generalizing c with
  | nil =>
    constructor
    · intro h
      exact ⟨c,rfl,h.symm⟩
    · rintro ⟨original,hc,hd⟩
      change c = original at hc
      subst original
      exact hd.symm
  | cons token tokens ih =>
    constructor
    · rintro ⟨next,hs,ht⟩
      rw [step_lift] at hs
      cases ho : m.step token c with
      | none => simp [ho] at hs
      | some originalNext =>
        have hn : liftCfg m trueSymbol originalNext = next :=
          Option.some.inj (by simpa only [ho,Option.map_some] using hs)
        subst next
        obtain ⟨original,hr,hd⟩ := (ih originalNext).mp ht
        exact ⟨original,⟨originalNext,ho,hr⟩,hd⟩
    · rintro ⟨original,⟨originalNext,hs,ht⟩,hd⟩
      refine ⟨liftCfg m trueSymbol originalNext,?_,(ih originalNext).mpr ⟨original,ht,hd⟩⟩
      rw [step_lift,hs]
      rfl

theorem trace_lift_iff (tokens : List (Option Bool)) (c d : m.Config) :
    (machine m trueSymbol).TraceValid tokens (liftCfg m trueSymbol c) (liftCfg m trueSymbol d) ↔
      m.TraceValid tokens c d := by
  rw [trace_recover]
  constructor
  · rintro ⟨original,ht,hd⟩
    have ho : d = original := lift_injective m trueSymbol hd
    subst original
    exact ht
  · intro ht
    exact ⟨d,ht,rfl⟩

theorem accepts_trace_iff (tokens : List (Option Bool)) (c : m.Config) :
    (∃ d, (machine m trueSymbol).TraceValid tokens (liftCfg m trueSymbol c) d ∧
      d.l = none ∧ acceptControl m d.var = true) ↔
        m.TraceValid tokens c (haltList m.core [trueSymbol]) := by
  constructor
  · rintro ⟨d,ht,hl,hv⟩
    obtain ⟨original,ho,hd⟩ := (trace_recover m trueSymbol tokens c d).mp ht
    subst d
    have hc := (endpoint_accepts_iff m trueSymbol original).mp ⟨hl,hv⟩
    simpa only [hc] using ho
  · intro ht
    have hc := (endpoint_accepts_iff m trueSymbol (haltList m.core [trueSymbol])).mpr rfl
    exact ⟨liftCfg m trueSymbol (haltList m.core [trueSymbol]),
      (trace_lift_iff m trueSymbol tokens c _).mpr ht,hc.1,hc.2⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
