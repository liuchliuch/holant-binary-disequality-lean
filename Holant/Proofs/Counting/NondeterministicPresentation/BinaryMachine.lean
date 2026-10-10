import Holant.Proofs.Counting.VerifierRun
import Mathlib.Data.Fintype.Pi


namespace Holant.LocalDrafts.CountingHardness.NondeterministicPresentation
open Turing Computability Holant.Complexity
open scoped BigOperators

structure BinaryMachine where
  core : FinTM2
  alternate : core.Λ → TM2.Stmt core.Γ core.Λ core.σ
  split : core.Λ → Bool
  alphabets : ∀ k, Fintype (core.Γ k)

namespace BinaryMachine
variable (m : BinaryMachine)
abbrev Config := m.core.Cfg
abbrev alternateComputer : FinTM2 := { m.core with m := m.alternate }

/-- None names the sole deterministic edge; a Bool names a genuine split edge.
The halted configuration has one canonical self-edge and no Bool edges. -/
def step (token : Option Bool) (c : m.Config) : Option m.Config :=
  match c.l, token with
  | none, none => some c
  | none, some _ => none
  | some label, none =>
      if m.split label then none else some (TM2.stepAux (m.core.m label) c.var c.stk)
  | some label, some b =>
      if m.split label then
        some (TM2.stepAux (if b then m.alternate label else m.core.m label) c.var c.stk)
      else none

@[simp] theorem step_halt (c : m.Config) (hc : c.l = none) :
    m.step none c = some c := by simp [step, hc]

@[simp] theorem step_halt_no_choice (c : m.Config) (hc : c.l = none) (b : Bool) :
    m.step (some b) c = none := by simp [step, hc]

/-- A branch log is consumed only at a split. It is an observer of actual
nondeterminism, never a stack or a primitive available to the machine. -/
def advance (s : List Bool × m.Config) : Option (List Bool × m.Config) :=
  match s.2.l with
  | none => some s
  | some label =>
      if m.split label then
        match s.1 with
        | [] => none
        | b :: rest => (m.step (some b) s.2).map (fun c => (rest, c))
      else (m.step none s.2).map (fun c => (s.1, c))

def run : ℕ → List Bool × m.Config → Option (List Bool × m.Config)
  | 0, s => some s
  | t + 1, s => (m.advance s).bind (run t)

theorem run_one (s : List Bool × m.Config) : m.run 1 s = m.advance s := by
  cases h : m.advance s <;> simp only [run,h,Option.bind_none,Option.bind_some]

theorem run_two (s : List Bool × m.Config) :
    m.run 2 s = (m.advance s).bind m.advance := by
  rw [run]
  cases h : m.advance s <;> simp only [h,Option.bind_none,Option.bind_some,run_one]

theorem run_add (t u : ℕ) (s : List Bool × m.Config) :
    m.run (t + u) s = (m.run u s).bind (m.run t) := by
  induction u generalizing s with
  | zero => rfl
  | succ u ih =>
      have hf : m.run (t+u) = (fun next => (m.run u next).bind (m.run t)) := funext ih
      calc
        m.run (t+(u+1)) s = (m.advance s).bind (m.run (t+u)) := rfl
        _ = (m.advance s).bind (fun next => (m.run u next).bind (m.run t)) :=
          congrArg (fun g => (m.advance s).bind g) hf
        _ = ((m.advance s).bind (m.run u)).bind (m.run t) := by
          cases m.advance s <;> rfl
        _ = (m.run (u+1) s).bind (m.run t) := rfl

theorem run_halt (t : ℕ) (log : List Bool) (c : m.Config) (hc : c.l = none) :
    m.run t (log, c) = some (log, c) := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [run, advance, hc, Option.bind_some] using ih

theorem prefix_exists (T j : ℕ) (start finish : List Bool × m.Config)
    (h : m.run T start = some finish) (hj : j ≤ T) :
    ∃ middle, m.run j start = some middle := by
  cases hp : m.run j start with
  | some middle => exact ⟨middle,rfl⟩
  | none =>
    rw [show T = (T - j) + j by omega,run_add,hp] at h
    cases h

/-- Exact branch-log trajectories; arbitrary extra rows are not witnesses. -/
def IsLogTrajectory (start : List Bool × m.Config) (t : ℕ)
    (rows : Fin (t + 1) → List Bool × m.Config) : Prop :=
  rows 0 = start ∧ ∀ i : Fin t, m.advance (rows i.castSucc) = some (rows i.succ)

def token (s : List Bool × m.Config) : Option Bool :=
  match s.2.l with
  | none => none
  | some l => if m.split l then s.1.head? else none

theorem advance_step (s next : List Bool × m.Config) (h : m.advance s = some next) :
    m.step (m.token s) s.2 = some next.2 := by
  cases hl : s.2.l with
  | none =>
    have hn : s = next := Option.some.inj (by simpa [advance,hl] using h)
    subst next
    simp [token,step,hl]
  | some l =>
    cases hs : m.split l with
    | false =>
      cases ht : m.step none s.2 with
      | none => simp [advance,hl,hs,ht] at h
      | some c =>
        have hn : (s.1,c) = next := Option.some.inj (by simpa [advance,hl,hs,ht] using h)
        subst next
        simpa [token,hl,hs] using ht
    | true =>
      cases hlog : s.1 with
      | nil => simp [advance,hl,hs,hlog] at h
      | cons b rest =>
        cases ht : m.step (some b) s.2 with
        | none => simp [advance,hl,hs,hlog,ht] at h
        | some c =>
          have hn : (rest,c) = next := Option.some.inj (by simpa [advance,hl,hs,hlog,ht] using h)
          subst next
          simpa [token,hl,hs,hlog] using ht

theorem advance_log (s next : List Bool × m.Config) (h : m.advance s = some next) :
    (m.token s).toList ++ next.1 = s.1 := by
  cases hl : s.2.l with
  | none =>
    have hn : s = next := Option.some.inj (by simpa [advance,hl] using h)
    subst next
    simp [token,hl]
  | some l =>
    cases hs : m.split l with
    | false =>
      cases ht : m.step none s.2 with
      | none => simp [advance,hl,hs,ht] at h
      | some c =>
        have hn : (s.1,c) = next := Option.some.inj (by simpa [advance,hl,hs,ht] using h)
        subst next
        simp [token,hl,hs]
    | true =>
      cases hlog : s.1 with
      | nil => simp [advance,hl,hs,hlog] at h
      | cons b rest =>
        cases ht : m.step (some b) s.2 with
        | none => simp [advance,hl,hs,hlog,ht] at h
        | some c =>
          have hn : (rest,c) = next := Option.some.inj (by simpa [advance,hl,hs,hlog,ht] using h)
          subst next
          simp [token,hl,hs,hlog]

theorem step_drive (token : Option Bool) (c d : m.Config) (rest : List Bool)
    (h : m.step token c = some d) :
    m.advance (token.toList ++ rest,c) = some (rest,d) ∧
      m.token (token.toList ++ rest,c) = token := by
  cases hl : c.l with
  | none =>
    cases token with
    | some b => simp [step,hl] at h
    | none =>
      have hd : c = d := Option.some.inj (by simpa [step,hl] using h)
      subst d
      simp [advance,BinaryMachine.token,hl]
  | some l =>
    cases hs : m.split l with
    | false =>
      cases token with
      | some b => simp [step,hl,hs] at h
      | none => simp [advance,BinaryMachine.token,hl,hs,h]
    | true =>
      cases token with
      | none => simp [step,hl,hs] at h
      | some b => simp [advance,BinaryMachine.token,hl,hs,h]

/-- A conventional finite list of labelled binary TM2 edges. Intermediate
configurations are quantified by actual step equations, with no simulation law. -/
def TraceValid : List (Option Bool) → m.Config → m.Config → Prop
  | [],c,d => c = d
  | bit :: rest,c,d => ∃ next, m.step bit c = some next ∧ TraceValid rest next d

def tokensOfRun : ℕ → List Bool × m.Config → List (Option Bool)
  | 0,_ => []
  | t+1,s => m.token s :: ((m.advance s).map (tokensOfRun t)).getD []

theorem reify_trace (bits : List (Option Bool)) (c d : m.Config)
    (h : m.TraceValid bits c d) :
    m.run bits.length (bits.filterMap id,c) = some ([],d) ∧
      m.tokensOfRun bits.length (bits.filterMap id,c) = bits := by
  induction bits generalizing c with
  | nil => subst d; exact ⟨rfl,rfl⟩
  | cons bit bits ih =>
    obtain ⟨next,hs,ht⟩ := h
    have hd := m.step_drive bit c next (bits.filterMap id) hs
    have hi := ih next ht
    have hlog : (bit :: bits).filterMap id = bit.toList ++ bits.filterMap id := by
      cases bit <;> rfl
    rw [List.length_cons,hlog]
    constructor
    · rw [run,hd.1,Option.bind_some]
      exact hi.1
    · rw [tokensOfRun,hd.1,hd.2]
      simpa only [Option.map_some,Option.getD_some] using congrArg (bit :: ·) hi.2

theorem run_trace (t : ℕ) (start finish : List Bool × m.Config)
    (h : m.run t start = some finish) :
    ∃ bits : List (Option Bool), bits.length = t ∧
      bits.filterMap id ++ finish.1 = start.1 ∧ m.TraceValid bits start.2 finish.2 := by
  induction t generalizing start with
  | zero =>
    have hs : start = finish := Option.some.inj h
    subst start
    exact ⟨[],rfl,rfl,rfl⟩
  | succ t ih =>
    cases hs : m.advance start with
    | none => simp [run,hs] at h
    | some next =>
      have ht : m.run t next = some finish := by simpa only [run,hs,Option.bind_some] using h
      obtain ⟨bits,hlen,hlog,hvalid⟩ := ih next ht
      refine ⟨m.token start :: bits,by simp only [List.length_cons,hlen],?_,
        next.2,m.advance_step start next hs,hvalid⟩
      have hb : (m.token start :: bits).filterMap id =
          (m.token start).toList ++ bits.filterMap id := by
        cases m.token start <;> rfl
      rw [hb,List.append_assoc,hlog]
      exact m.advance_log start next hs

def IsTrajectory (start : m.Config) (t : ℕ) (tokens : Fin t → Option Bool)
    (rows : Fin (t + 1) → m.Config) : Prop :=
  rows 0 = start ∧ ∀ i : Fin t, m.step (tokens i) (rows i.castSucc) = some (rows i.succ)

theorem erase_log_trajectory (start : List Bool × m.Config) (t : ℕ)
    (rows : Fin (t + 1) → List Bool × m.Config) (h : m.IsLogTrajectory start t rows) :
    m.IsTrajectory start.2 t (fun i => m.token (rows i.castSucc)) (fun i => (rows i).2) :=
  ⟨congrArg Prod.snd h.1,fun i => m.advance_step _ _ (h.2 i)⟩

theorem physical_trajectory_unique (start : m.Config) (t : ℕ) (bits : Fin t → Option Bool)
    (rows other : Fin (t + 1) → m.Config)
    (hr : m.IsTrajectory start t bits rows) (ho : m.IsTrajectory start t bits other) :
    rows = other := by
  have he : ∀ (j : ℕ) (hj : j < t + 1), rows ⟨j,hj⟩ = other ⟨j,hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; exact hr.1.trans ho.1.symm
    | succ j ih =>
      intro hj
      have hjt : j < t := by omega
      have hs := hr.2 ⟨j,hjt⟩
      have ht := ho.2 ⟨j,hjt⟩
      change m.step (bits ⟨j,hjt⟩) (rows ⟨j,by omega⟩) = some (rows ⟨j+1,hj⟩) at hs
      change m.step (bits ⟨j,hjt⟩) (other ⟨j,by omega⟩) = some (other ⟨j+1,hj⟩) at ht
      rw [ih (by omega)] at hs
      exact Option.some.inj (hs.symm.trans ht)
  funext i
  exact he i.val i.isLt

theorem trajectory_unique (start : List Bool × m.Config) (t : ℕ)
    (rows other : Fin (t + 1) → List Bool × m.Config)
    (hr : m.IsLogTrajectory start t rows) (ho : m.IsLogTrajectory start t other) :
    rows = other := by
  have he : ∀ (j : ℕ) (hj : j < t + 1), rows ⟨j, hj⟩ = other ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; exact hr.1.trans ho.1.symm
    | succ j ih =>
      intro hj
      have hjt : j < t := by omega
      have hs := hr.2 ⟨j, hjt⟩
      have ht := ho.2 ⟨j, hjt⟩
      change m.advance (rows ⟨j, by omega⟩) = some (rows ⟨j + 1, hj⟩) at hs
      change m.advance (other ⟨j, by omega⟩) = some (other ⟨j + 1, hj⟩) at ht
      rw [ih (by omega)] at hs
      exact Option.some.inj (hs.symm.trans ht)
  funext i
  exact he i.val i.isLt

local instance : Fintype m.core.Λ := m.core.ΛFin

def pushBudget : ℕ := VerifierRun.pushBudget m.core + VerifierRun.pushBudget m.alternateComputer

theorem step_stack_bound (token : Option Bool) (c d : m.Config) (B : ℕ)
    (hc : ∀ k, (c.stk k).length ≤ B) (h : m.step token c = some d) :
    ∀ k, (d.stk k).length ≤ B + m.pushBudget := by
  cases hl : c.l with
  | none =>
    cases token with
    | some b => simp [step, hl] at h
    | none =>
      have hd : c = d := Option.some.inj (by simpa [step, hl] using h)
      subst d
      intro k
      exact (hc k).trans (Nat.le_add_right _ _)
  | some label =>
    cases token with
    | none =>
      cases hs : m.split label with
      | true => simp [step, hl, hs] at h
      | false =>
        have hd : VerifierRun.holdStep m.core c = d :=
          Option.some.inj (by simpa [step, hl, hs, VerifierRun.holdStep] using h)
        subst d
        intro k
        exact (VerifierRun.holdStep_stack_bound m.core c B hc k).trans
          (Nat.add_le_add_left (Nat.le_add_right _ _) B)
    | some b =>
      cases hs : m.split label with
      | false => simp [step, hl, hs] at h
      | true =>
        cases b with
        | false =>
          have hd : VerifierRun.holdStep m.core c = d :=
            Option.some.inj (by simpa [step, hl, hs, VerifierRun.holdStep] using h)
          subst d
          intro k
          exact (VerifierRun.holdStep_stack_bound m.core c B hc k).trans
            (Nat.add_le_add_left (Nat.le_add_right _ _) B)
        | true =>
          intro k
          have hlen : ((TM2.stepAux (m.alternate label) c.var c.stk).stk k).length =
              (d.stk k).length := by
            have hs' : (some (TM2.stepAux (m.alternate label) c.var c.stk) : Option m.Config) =
                some d := by
              simpa [step, hl, hs] using h
            have hd : (TM2.stepAux (m.alternate label) c.var c.stk : m.Config) = d :=
              Option.some.inj hs'
            exact congrArg (fun z : m.Config => (z.stk k).length) hd
          have hp : VerifierRun.pushes (m.alternate label) ≤
              VerifierRun.pushBudget m.alternateComputer := by
            change VerifierRun.pushes (m.alternate label) ≤
              ∑ j : m.core.Λ, VerifierRun.pushes (m.alternate j)
            exact Finset.single_le_sum (f := fun j : m.core.Λ => VerifierRun.pushes (m.alternate j))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)
          have hbudget : VerifierRun.pushes (m.alternate label) ≤ m.pushBudget := by
            change VerifierRun.pushes (m.alternate label) ≤
              VerifierRun.pushBudget m.core + VerifierRun.pushBudget m.alternateComputer
            exact hp.trans (Nat.le_add_left _ _)
          have hb := VerifierRun.stepAux_stack_bound (m.alternate label) c.var c.stk B hc k
          rw [hlen] at hb
          exact hb.trans (Nat.add_le_add_left hbudget B)

theorem advance_stack_bound (s next : List Bool × m.Config) (B : ℕ)
    (hc : ∀ k, (s.2.stk k).length ≤ B) (h : m.advance s = some next) :
    ∀ k, (next.2.stk k).length ≤ B + m.pushBudget := by
  cases hl : s.2.l with
  | none =>
    have hn : s = next := Option.some.inj (by simpa [advance, hl] using h)
    subst next
    intro k
    exact (hc k).trans (Nat.le_add_right _ _)
  | some label =>
    cases hs : m.split label with
    | false =>
      cases ht : m.step none s.2 with
      | none => simp [advance, hl, hs, ht] at h
      | some c =>
        have hn : (s.1,c) = next := Option.some.inj (by simpa [advance, hl, hs, ht] using h)
        subst next
        exact m.step_stack_bound none s.2 c B hc ht
    | true =>
      cases hlog : s.1 with
      | nil => simp [advance, hl, hs, hlog] at h
      | cons b rest =>
        cases ht : m.step (some b) s.2 with
        | none => simp [advance, hl, hs, hlog, ht] at h
        | some c =>
          have hn : (rest,c) = next := Option.some.inj
            (by simpa [advance, hl, hs, hlog, ht] using h)
          subst next
          exact m.step_stack_bound (some b) s.2 c B hc ht

theorem run_stack_bound (t : ℕ) (s next : List Bool × m.Config) (B : ℕ)
    (hc : ∀ k, (s.2.stk k).length ≤ B) (h : m.run t s = some next) :
    ∀ k, (next.2.stk k).length ≤ B + t * m.pushBudget := by
  induction t generalizing s B with
  | zero =>
    have hn : s = next := Option.some.inj h
    subst next
    simpa only [Nat.zero_mul, Nat.add_zero] using hc
  | succ t ih =>
    cases hs : m.advance s with
    | none => simp [run, hs] at h
    | some middle =>
      have hm := m.advance_stack_bound s middle B hc hs
      have ht : m.run t middle = some next := by simpa only [run, hs, Option.bind_some] using h
      have hb := ih middle (B + m.pushBudget) hm ht
      simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

end BinaryMachine
end Holant.LocalDrafts.CountingHardness.NondeterministicPresentation
