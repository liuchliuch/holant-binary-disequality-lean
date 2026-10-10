import Holant.Complexity.MachineReturn

/-!
# Structural binary-machine embedding with a prescribed return

The compiler only traverses finite TM2 syntax. The stack representation and state
representation laws below are proved by each client; they are simulation data,
not operations available to a running machine. In particular `lift` is never
invoked by a statement.
-/

namespace Holant.Complexity.BinaryCompose
open Turing

variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]

/-- A stack injection and a compatible mathematical representation of tapes. -/
structure StackEmbedding (K J : Type) [DecidableEq K] [DecidableEq J] where
  key : K → J
  lift : (K → List Bool) → J → List Bool
  lookup : ∀ tapes k, lift tapes (key k) = tapes k
  update : ∀ tapes k word,
    Function.update (lift tapes) (key k) word = lift (Function.update tapes k word)

/-- Finite-state injection, with a left inverse used by compiled instructions. -/
structure StateEmbedding (σ τ : Type) where
  put : σ → τ
  get : τ → σ
  get_put : ∀ state, get (put state) = state

/-- A prescribed return label replaces halt; `none` retains genuine halt. -/
def embedStmt (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R) :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : J => Bool) R τ
  | .push k f q => .push (layout.key k) (fun v => f (states.get v))
      (embedStmt layout states labels stop q)
  | .pop k f q => .pop (layout.key k) (fun v b => states.put (f (states.get v) b))
      (embedStmt layout states labels stop q)
  | .peek k f q => .peek (layout.key k) (fun v b => states.put (f (states.get v) b))
      (embedStmt layout states labels stop q)
  | .load f q => .load (fun v => states.put (f (states.get v)))
      (embedStmt layout states labels stop q)
  | .branch f a b => .branch (fun v => f (states.get v))
      (embedStmt layout states labels stop a) (embedStmt layout states labels stop b)
  | .goto f => .goto (fun v => labels (f (states.get v)))
  | .halt => match stop with
    | none => .halt
    | some label => .goto (fun _ => label)

def embedCfg (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : J => Bool) R τ where
  l := c.l.elim stop (fun label => some (labels label))
  var := states.put c.var
  stk := layout.lift c.stk

/-- Exact semantics, including the replaced halting transition. -/
theorem embed_stepAux (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (tapes : K → List Bool) :
    TM2.stepAux (embedStmt layout states labels stop q) (states.put v) (layout.lift tapes) =
      embedCfg layout states labels stop (TM2.stepAux q v tapes) := by
  induction q generalizing v tapes with
  | push k f q ih =>
    simpa only [embedStmt, TM2.stepAux, states.get_put, layout.lookup, layout.update] using
      ih v (Function.update tapes k (f v :: tapes k))
  | pop k f q ih =>
    simpa only [embedStmt, TM2.stepAux, states.get_put, layout.lookup, layout.update] using
      ih (f v (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | peek k f q ih =>
    simpa only [embedStmt, TM2.stepAux, states.get_put, layout.lookup] using
      ih (f v (tapes k).head?) tapes
  | load f q ih =>
    simpa only [embedStmt, TM2.stepAux, states.get_put] using ih (f v) tapes
  | branch f a b ha hb =>
    cases h : f v <;> simp [embedStmt, TM2.stepAux, states.get_put, h, ha, hb]
  | goto f => simp [embedStmt, TM2.stepAux, embedCfg, states.get_put]
  | halt => cases stop <;> rfl

/-- Embedding never increases the elementary-instruction budget. -/
theorem embed_budget (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (embedStmt layout states labels stop q) = TM2Cost.budget q := by
  induction q <;> simp [embedStmt, TM2Cost.budget, *]
  cases stop <;> rfl

/-- The ambient program need only agree at the embedded source labels. -/
theorem embed_step (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R τ)
    (agree : ∀ label, target (labels label) = embedStmt layout states labels stop (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source c = some d) :
    TM2.step target (embedCfg layout states labels stop c) =
      some (embedCfg layout states labels stop d) := by
  rcases c with ⟨label, v, tapes⟩
  cases label with
  | none => simp [TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (source label) v tapes = d := Option.some.inj h
    subst d
    simp only [embedCfg, Option.elim_some, TM2.step, agree, embed_stepAux]

/-- Exact runs lift through the entire finite source computation. -/
theorem embed_run (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R τ)
    (agree : ∀ label, target (labels label) = embedStmt layout states labels stop (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (n : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) :
    (fun p => p.bind (TM2.step target))^[n]
      (some (embedCfg layout states labels stop c)) = some (embedCfg layout states labels stop d) := by
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
      rw [Function.iterate_succ_apply', ih previous hp]
      exact embed_step layout states labels stop source target agree previous d hs

end Holant.Complexity.BinaryCompose
