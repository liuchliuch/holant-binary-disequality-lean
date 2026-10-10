import Holant.Complexity.BinaryCompose.Embed


namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
open _root_.Holant.Complexity


/-! A structural returning compiler with explicitly injected finite labels. It
retains arbitrary finite caller memory and untouched binary-stack frames. The
layout's tape representation occurs only in proofs, never in instructions. -/
namespace Holant.Complexity.RationalArithmetic.Call
open Turing BinaryCompose
variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]

def stmt (layout : StackEmbedding K J) (labels : Λ → R) (ret : τ → R) :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : J => Bool) R (σ × τ)
  | .push k f q => .push (layout.key k) (fun v => f v.1) (stmt layout labels ret q)
  | .pop k f q => .pop (layout.key k) (fun v bit => (f v.1 bit, v.2)) (stmt layout labels ret q)
  | .peek k f q => .peek (layout.key k) (fun v bit => (f v.1 bit, v.2)) (stmt layout labels ret q)
  | .load f q => .load (fun v => (f v.1, v.2)) (stmt layout labels ret q)
  | .branch f a b => .branch (fun v => f v.1) (stmt layout labels ret a) (stmt layout labels ret b)
  | .goto f => .goto (fun v => labels (f v.1))
  | .halt => .goto (fun v => ret v.2)


/-- Only the fixed stack-key map enters generated syntax. -/
theorem stmt_key_congr (a b : StackEmbedding K J) (h : a.key = b.key)
    (labels : Λ → R) (ret : τ → R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    stmt a labels ret q = stmt b labels ret q := by
  induction q <;> simp [stmt, *]

def cfg (layout : StackEmbedding K J) (labels : Λ → R) (ret : τ → R)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ) :
    TM2.Cfg (fun _ : J => Bool) R (σ × τ) where
  l := some (c.l.elim (ret memory) labels)
  var := (c.var, memory)
  stk := layout.lift c.stk

theorem stepAux_stmt (layout : StackEmbedding K J) (labels : Λ → R) (ret : τ → R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (tapes : K → List Bool) (memory : τ) :
    TM2.stepAux (stmt layout labels ret q) (v, memory) (layout.lift tapes) =
      cfg layout labels ret (TM2.stepAux q v tapes) memory := by
  induction q generalizing v tapes with
  | push k f q ih =>
    simpa only [stmt, TM2.stepAux, layout.lookup, layout.update] using
      ih v (Function.update tapes k (f v :: tapes k))
  | pop k f q ih =>
    simpa only [stmt, TM2.stepAux, layout.lookup, layout.update] using
      ih (f v (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | peek k f q ih => simpa only [stmt, TM2.stepAux, layout.lookup] using ih (f v (tapes k).head?) tapes
  | load f q ih => simpa only [stmt, TM2.stepAux] using ih (f v) tapes
  | branch f a b ha hb => cases h : f v <;> simp [stmt, TM2.stepAux, h, ha, hb]
  | goto f => rfl
  | halt => rfl

theorem budget_stmt (layout : StackEmbedding K J) (labels : Λ → R) (ret : τ → R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (stmt layout labels ret q) = TM2Cost.budget q := by
  induction q <;> simp [stmt, TM2Cost.budget, *]

theorem step (layout : StackEmbedding K J) (labels : Λ → R) (ret : τ → R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R (σ × τ))
    (agree : ∀ label, target (labels label) = stmt layout labels ret (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ)
    (h : TM2.step source c = some d) :
    TM2.step target (cfg layout labels ret c memory) = some (cfg layout labels ret d memory) := by
  rcases c with ⟨label, v, tapes⟩
  cases label with
  | none => simp [TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (source label) v tapes = d := Option.some.inj h
    subst d
    simp only [cfg, Option.elim_some, TM2.step, agree, stepAux_stmt]

theorem run (layout : StackEmbedding K J) (labels : Λ → R) (ret : τ → R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R (σ × τ))
    (agree : ∀ label, target (labels label) = stmt layout labels ret (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (memory : τ) (n : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) :
    (fun p => p.bind (TM2.step target))^[n]
      (some (cfg layout labels ret c memory)) = some (cfg layout labels ret d memory) := by
  induction n generalizing d with
  | zero => have hd := Option.some.inj h; subst d; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step source))^[n] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : TM2.step source previous = some d := by simpa [hp] using h
      rw [Function.iterate_succ_apply', ih previous hp]
      exact step layout labels ret source target agree previous d memory hs

end Holant.Complexity.RationalArithmetic.Call

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
