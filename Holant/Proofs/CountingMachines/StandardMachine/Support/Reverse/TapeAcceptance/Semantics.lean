import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.TapeAcceptance.Program

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The finite control verdict is proved from the actual
pop/peek/restore statement. In particular singleton output, full output EOF,
reset source state and all other tapes empty are checked inside the program. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (trueSymbol : m.core.Γ m.core.k₁)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance : DecidableEq m.core.σ := Classical.decEq _
local instance : DecidableEq (m.core.Γ m.core.k₁) := Classical.decEq _

theorem scan_stepAux (ks : List m.core.K) (v : State m)
    (S : ∀ k, List (m.core.Γ k)) :
    TM2.stepAux (scan m ks) v S =
      ⟨none,(v.1,none,scanVerdict m ks S v.2.2),S⟩ := by
  induction ks generalizing v with
  | nil => rfl
  | cons k ks ih =>
    by_cases hk : k = m.core.k₁
    · simp only [scan,scanVerdict,hk,if_pos,ih]
    · have hh : (S k).head?.isNone = (S k).isEmpty := by cases S k <;> rfl
      simpa [scan,scanVerdict,hk,TM2.stepAux,hh] using
        ih (v.1,v.2.1,v.2.2 && (S k).head?.isNone)

theorem scanVerdict_false (ks : List m.core.K) (S : ∀ k, List (m.core.Γ k)) :
    scanVerdict m ks S false = false := by
  induction ks with
  | nil => rfl
  | cons k ks ih => by_cases hk : k = m.core.k₁ <;> simp [scanVerdict,hk,ih]

theorem scanVerdict_true_iff (ks : List m.core.K) (S : ∀ k, List (m.core.Γ k)) (b : Bool) :
    scanVerdict m ks S b = true ↔ b = true ∧ ∀ k ∈ ks, k ≠ m.core.k₁ → S k = [] := by
  induction ks generalizing b with
  | nil => simp [scanVerdict]
  | cons k ks ih =>
    by_cases hk : k = m.core.k₁
    · simp [scanVerdict,hk,ih]
    · simp [scanVerdict,hk,ih,and_assoc,and_left_comm,and_comm]

theorem key_mem (k : m.core.K) : k ∈ keys m := by
  rw [keys,List.mem_ofFn']
  exact ⟨Fintype.equivFin m.core.K k,(Fintype.equivFin m.core.K).symm_apply_apply k⟩

/-- No clean-tape assumption is used: even a wrong head, extra output symbol,
non-reset state, or dirty unused tape is read and rejected by the same code. -/
theorem observer_stepAux (v : State m) (S : ∀ k, List (m.core.Γ k)) :
    TM2.stepAux (observer m trueSymbol) v S =
      ⟨none,(v.1,none,tapeVerdict m trueSymbol v.1 S),S⟩ := by
  cases hhead : S m.core.k₁ with
  | nil =>
    have hu : Function.update S m.core.k₁ [] = S := by
      simpa only [hhead] using Function.update_eq_self m.core.k₁ S
    simp [observer,TM2.stepAux,hhead,hu,scan_stepAux,tapeVerdict,scanVerdict_false]
  | cons head tail =>
    have hr : Function.update (Function.update S m.core.k₁ tail)
        m.core.k₁ (head::tail) = S := by
      rw [Function.update_idem]
      simpa only [hhead] using Function.update_eq_self m.core.k₁ S
    cases tail with
    | nil =>
      simp [observer,TM2.stepAux,hhead,hr,scan_stepAux,tapeVerdict,Bool.and_assoc]
    | cons next rest =>
      simp [observer,TM2.stepAux,hhead,hr,scan_stepAux,tapeVerdict,scanVerdict_false]

theorem tapeVerdict_true_iff (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) :
    tapeVerdict m trueSymbol v S = true ↔
      v = m.core.initialState ∧ S m.core.k₁ = [trueSymbol] ∧
        ∀ k, k ≠ m.core.k₁ → S k = [] := by
  rw [tapeVerdict,scanVerdict_true_iff]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hv,ho⟩,hs⟩
    exact ⟨hv,ho,fun k hk => hs k (key_mem m k) hk⟩
  · rintro ⟨hv,ho,hs⟩
    exact ⟨⟨hv,ho⟩,fun k _ hk => hs k hk⟩

/-- The literal observer is equivalent to the original clean true terminal;
this is an output theorem, not a caller-provided accepting-control law. -/
theorem endpoint_accepts_iff (c : m.Config) :
    (liftCfg m trueSymbol c).l = none ∧
      acceptControl m (liftCfg m trueSymbol c).var = true ↔
        c = haltList m.core [trueSymbol] := by
  constructor
  · rintro ⟨hl,hv⟩
    have hlc : c.l = none := hl
    have ht : tapeVerdict m trueSymbol c.var c.stk = true := by
      simpa only [liftCfg,acceptControl,hlc,Option.isNone_none,if_true] using hv
    obtain ⟨hs,ho,hclean⟩ := (tapeVerdict_true_iff m trueSymbol _ _).mp ht
    rcases c with ⟨l,v,S⟩
    simp only at hlc hs ho hclean
    subst l
    subst v
    congr 1
    funext k
    by_cases hk : k = m.core.k₁
    · subst k; simpa [haltList] using ho
    · simpa [haltList,hk] using hclean k hk
  · intro hc
    subst c
    have hv : tapeVerdict m trueSymbol m.core.initialState
        (haltList m.core [trueSymbol]).stk = true :=
      (tapeVerdict_true_iff m trueSymbol _ _).mpr
        ⟨rfl,by simp [haltList],fun k hk => by simp [haltList,hk]⟩
    exact ⟨rfl,by simpa only [liftCfg,haltList,acceptControl,Option.isNone_none,if_true] using hv⟩

theorem statement_stepAux (q : m.core.Stmt) (v : m.core.σ)
    (S : ∀ k, List (m.core.Γ k)) :
    TM2.stepAux (statement m trueSymbol q) (clear m v) S =
      liftCfg m trueSymbol (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa only [statement,TM2.stepAux,clear] using ih v _
  | pop k f q ih => simpa only [statement,TM2.stepAux,clear] using ih _ _
  | peek k f q ih => simpa only [statement,TM2.stepAux,clear] using ih _ S
  | load f q ih => simpa only [statement,TM2.stepAux,clear] using ih _ S
  | branch f q r hq hr =>
    cases h : f v <;> simp only [statement,TM2.stepAux,clear,h,Bool.false_eq_true,if_false,if_true] <;> first | exact hq v S | exact hr v S
  | goto f => rfl
  | halt => exact observer_stepAux m trueSymbol (clear m v) S

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
