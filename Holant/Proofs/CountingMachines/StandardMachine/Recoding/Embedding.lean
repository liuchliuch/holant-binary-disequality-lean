import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Source

set_option backward.isDefEq.respectTransparency false
/-! Structural embeddings of heterogeneous finite-stack programs. Stack and
state maps below describe representations only. Executable instructions use
finite symbol equivalences and finite state projections, never whole tapes. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding.Embedding
open Turing
variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]
variable {A : K → Type} {B : J → Type}

structure Layout (A : K → Type) (B : J → Type) where
  key : K → J
  symbol : ∀ k, A k ≃ B (key k)
  lift : (∀ k, List (A k)) → ∀ j, List (B j)
  lookup : ∀ tapes k, lift tapes (key k) = (tapes k).map (symbol k)
  update : ∀ tapes k word,
    Function.update (lift tapes) (key k) (word.map (symbol k)) =
      lift (Function.update tapes k word)

structure States (σ τ : Type) where
  put : σ → τ
  get : τ → σ
  get_put : ∀ v, get (put v) = v

def stmt (layout : Layout A B) (states : States σ τ) (labels : Λ → R) (stop : Option R) :
    TM2.Stmt A Λ σ → TM2.Stmt B R τ
  | .push k f q => .push (layout.key k) (fun v => layout.symbol k (f (states.get v)))
      (stmt layout states labels stop q)
  | .pop k f q => .pop (layout.key k)
      (fun v a => states.put (f (states.get v) (a.map (layout.symbol k).symm)))
      (stmt layout states labels stop q)
  | .peek k f q => .peek (layout.key k)
      (fun v a => states.put (f (states.get v) (a.map (layout.symbol k).symm)))
      (stmt layout states labels stop q)
  | .load f q => .load (fun v => states.put (f (states.get v))) (stmt layout states labels stop q)
  | .branch f q r => .branch (fun v => f (states.get v))
      (stmt layout states labels stop q) (stmt layout states labels stop r)
  | .goto f => .goto (fun v => labels (f (states.get v)))
  | .halt => match stop with
      | none => .halt
      | some label => .goto (fun _ => label)

def cfg (layout : Layout A B) (states : States σ τ) (labels : Λ → R) (stop : Option R)
    (c : TM2.Cfg A Λ σ) : TM2.Cfg B R τ :=
  ⟨c.l.elim stop (fun l => some (labels l)),states.put c.var,layout.lift c.stk⟩

theorem stepAux (layout : Layout A B) (states : States σ τ) (labels : Λ → R) (stop : Option R)
    (q : TM2.Stmt A Λ σ) (v : σ) (tapes : ∀ k, List (A k)) :
    TM2.stepAux (stmt layout states labels stop q) (states.put v) (layout.lift tapes) =
      cfg layout states labels stop (TM2.stepAux q v tapes) := by
  induction q generalizing v tapes with
  | push k f q ih =>
      simpa only [stmt,TM2.stepAux,states.get_put,layout.lookup,← List.map_cons,layout.update] using
        ih v (Function.update tapes k (f v :: tapes k))
  | pop k f q ih =>
      simpa [stmt,TM2.stepAux,states.get_put,layout.lookup,← List.map_tail,layout.update] using
        ih (f v (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | peek k f q ih =>
      simpa [stmt,TM2.stepAux,states.get_put,layout.lookup] using ih (f v (tapes k).head?) tapes
  | load f q ih => simpa only [stmt,TM2.stepAux,states.get_put] using ih (f v) tapes
  | branch f q r hq hr =>
      cases h : f v <;> simp [stmt,TM2.stepAux,states.get_put,h,hq,hr]
  | goto f => simp [stmt,TM2.stepAux,cfg,states.get_put]
  | halt => cases stop <;> rfl

theorem step (layout : Layout A B) (states : States σ τ) (labels : Λ → R) (stop : Option R)
    (source : Λ → TM2.Stmt A Λ σ) (target : R → TM2.Stmt B R τ)
    (agree : ∀ l, target (labels l) = stmt layout states labels stop (source l))
    (c d : TM2.Cfg A Λ σ) (h : TM2.step source c = some d) :
    TM2.step target (cfg layout states labels stop c) = some (cfg layout states labels stop d) := by
  rcases c with ⟨label,v,tapes⟩
  cases label with
  | none => simp [TM2.step] at h
  | some label =>
      have hd : TM2.stepAux (source label) v tapes = d := Option.some.inj h
      subst d
      simp only [cfg,Option.elim_some,TM2.step,agree,stepAux]

theorem run (layout : Layout A B) (states : States σ τ) (labels : Λ → R) (stop : Option R)
    (source : Λ → TM2.Stmt A Λ σ) (target : R → TM2.Stmt B R τ)
    (agree : ∀ l, target (labels l) = stmt layout states labels stop (source l))
    (c d : TM2.Cfg A Λ σ) (n : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) :
    (fun p => p.bind (TM2.step target))^[n] (some (cfg layout states labels stop c)) =
      some (cfg layout states labels stop d) := by
  induction n generalizing d with
  | zero => have hd := Option.some.inj h; subst d; rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at h
      cases hp : (fun p => p.bind (TM2.step source))^[n] (some c) with
      | none => simp [hp] at h
      | some previous =>
          have hs : TM2.step source previous = some d := by simpa [hp] using h
          rw [Function.iterate_succ_apply',ih previous hp]
          exact step layout states labels stop source target agree previous d hs

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding.Embedding
