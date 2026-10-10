import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Semantics
import Holant.Proofs.CountingMachines.StandardMachine.Support.Cost

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. A literal injection of heterogeneous stack syntax.
`merge` and configuration views occur only in proofs, never in instructions. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.HeterogeneousSum
open Turing Holant.Complexity BinaryCompose
variable {J K Λ R σ τ : Type} [DecidableEq J] [DecidableEq K]
    (Δ : J → Type) (Γ : K → Type)

def Alphabet : J ⊕ K → Type
  | .inl j => Δ j
  | .inr k => Γ k

def merge (left : ∀ j, List (Δ j)) (right : ∀ k, List (Γ k)) :
    ∀ key, List (Alphabet Δ Γ key)
  | .inl j => left j
  | .inr k => right k

theorem update_left (left : ∀ j, List (Δ j)) (right : ∀ k, List (Γ k))
    (j : J) (word : List (Δ j)) :
    Function.update (merge Δ Γ left right) (.inl j) word =
      merge Δ Γ (Function.update left j word) right := by
  funext key
  cases key with
  | inl k => by_cases h : k = j <;> simp [merge,h]
  | inr k => simp [merge]

theorem update_right (left : ∀ j, List (Δ j)) (right : ∀ k, List (Γ k))
    (k : K) (word : List (Γ k)) :
    Function.update (merge Δ Γ left right) (.inr k) word =
      merge Δ Γ left (Function.update right k word) := by
  funext key
  cases key with
  | inl j => simp [merge]
  | inr j => by_cases h : j = k <;> simp [merge,h]

def rightStmt (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R) :
    TM2.Stmt Γ Λ σ → TM2.Stmt (Alphabet Δ Γ) R τ
  | .push k f q => .push (.inr k) (fun v => f (states.get v))
      (rightStmt states labels stop q)
  | .pop k f q => .pop (.inr k) (fun v b => states.put (f (states.get v) b))
      (rightStmt states labels stop q)
  | .peek k f q => .peek (.inr k) (fun v b => states.put (f (states.get v) b))
      (rightStmt states labels stop q)
  | .load f q => .load (fun v => states.put (f (states.get v)))
      (rightStmt states labels stop q)
  | .branch f q r => .branch (fun v => f (states.get v))
      (rightStmt states labels stop q) (rightStmt states labels stop r)
  | .goto f => .goto (fun v => labels (f (states.get v)))
  | .halt => stop.elim .halt (fun label => .goto (fun _ => label))

def rightCfg (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (left : ∀ j, List (Δ j)) (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg (Alphabet Δ Γ) R τ :=
  ⟨c.l.elim stop (fun l => some (labels l)),states.put c.var,merge Δ Γ left c.stk⟩

theorem right_stepAux (states : StateEmbedding σ τ) (labels : Λ → R)
    (stop : Option R) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (left : ∀ j, List (Δ j)) (right : ∀ k, List (Γ k)) :
    TM2.stepAux (rightStmt Δ Γ states labels stop q) (states.put v)
      (merge Δ Γ left right) =
        rightCfg Δ Γ states labels stop left (TM2.stepAux q v right) := by
  induction q generalizing v right with
  | push k f q ih =>
    simpa only [rightStmt,TM2.stepAux,merge,states.get_put,update_right] using ih v _
  | pop k f q ih =>
    simpa only [rightStmt,TM2.stepAux,merge,states.get_put,update_right] using ih _ _
  | peek k f q ih =>
    simpa only [rightStmt,TM2.stepAux,merge,states.get_put] using ih _ right
  | load f q ih => simpa only [rightStmt,TM2.stepAux,states.get_put] using ih _ right
  | branch f q r hq hr =>
    cases h : f v <;> simp [rightStmt,TM2.stepAux,states.get_put,h,hq,hr]
  | goto f => simp [rightStmt,TM2.stepAux,rightCfg,states.get_put]
  | halt => cases stop <;> rfl

theorem right_budget (states : StateEmbedding σ τ) (labels : Λ → R)
    (stop : Option R) (q : TM2.Stmt Γ Λ σ) :
    HeterogeneousCost.budget (rightStmt Δ Γ states labels stop q) =
      HeterogeneousCost.budget q := by
  induction q <;> simp [rightStmt,HeterogeneousCost.budget, *]
  cases stop <;> rfl

def restateStmt (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R) :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ R τ
  | .push k f q => .push k (fun v => f (states.get v)) (restateStmt states labels stop q)
  | .pop k f q => .pop k (fun v b => states.put (f (states.get v) b))
      (restateStmt states labels stop q)
  | .peek k f q => .peek k (fun v b => states.put (f (states.get v) b))
      (restateStmt states labels stop q)
  | .load f q => .load (fun v => states.put (f (states.get v)))
      (restateStmt states labels stop q)
  | .branch f q r => .branch (fun v => f (states.get v))
      (restateStmt states labels stop q) (restateStmt states labels stop r)
  | .goto f => .goto (fun v => labels (f (states.get v)))
  | .halt => stop.elim .halt (fun label => .goto (fun _ => label))

def restateCfg (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ R τ :=
  ⟨c.l.elim stop (fun l => some (labels l)),states.put c.var,c.stk⟩

theorem restate_stepAux (states : StateEmbedding σ τ) (labels : Λ → R)
    (stop : Option R) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (restateStmt Γ states labels stop q) (states.put v) S =
      restateCfg Γ states labels stop (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa only [restateStmt,TM2.stepAux,states.get_put] using ih v _
  | pop k f q ih => simpa only [restateStmt,TM2.stepAux,states.get_put] using ih _ _
  | peek k f q ih => simpa only [restateStmt,TM2.stepAux,states.get_put] using ih _ S
  | load f q ih => simpa only [restateStmt,TM2.stepAux,states.get_put] using ih _ S
  | branch f q r hq hr =>
    cases h : f v <;> simp [restateStmt,TM2.stepAux,states.get_put,h,hq,hr]
  | goto f => simp [restateStmt,TM2.stepAux,restateCfg,states.get_put]
  | halt => cases stop <;> rfl

theorem restate_step (states : StateEmbedding σ τ) (labels : Λ → R)
    (stop : Option R) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : R → TM2.Stmt Γ R τ)
    (agree : ∀ l, target (labels l) = restateStmt Γ states labels stop (source l))
    (c d : TM2.Cfg Γ Λ σ) (h : TM2.step source c = some d) :
    TM2.step target (restateCfg Γ states labels stop c) =
      some (restateCfg Γ states labels stop d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    have hd : TM2.stepAux (source l) v S = d := Option.some.inj h
    subst d
    simp only [restateCfg,Option.elim_some,TM2.step,agree,restate_stepAux]

theorem restate_run (states : StateEmbedding σ τ) (labels : Λ → R)
    (stop : Option R) (source : Λ → TM2.Stmt Γ Λ σ)
    (target : R → TM2.Stmt Γ R τ)
    (agree : ∀ l, target (labels l) = restateStmt Γ states labels stop (source l))
    (n : ℕ) (c d : TM2.Cfg Γ Λ σ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) :
    (fun p => p.bind (TM2.step target))^[n]
      (some (restateCfg Γ states labels stop c)) =
        some (restateCfg Γ states labels stop d) := by
  induction n generalizing d with
  | zero =>
    have hd : c = d := Option.some.inj h
    subst d
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step source))^[n] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : TM2.step source previous = some d := by simpa [hp] using h
      rw [Function.iterate_succ_apply',ih previous hp]
      exact restate_step Γ states labels stop source target agree previous d hs

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.HeterogeneousSum
