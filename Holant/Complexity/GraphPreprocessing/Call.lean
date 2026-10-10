import Holant.Complexity.GraphPreprocessing.Returning
import Holant.Complexity.GraphPreprocessing.Frame

/-! Structurally embed clean finite subroutines with an arbitrary preserved stack
frame and a proved finite-state embedding. This is ordinary TM2 syntax and exact
execution, not a host callback on words or configurations. -/
namespace Holant.Complexity.GraphPreprocessing.Call
open Turing BinaryCompose
variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]

def statement (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) : TM2.Stmt (fun _ : K ⊕ J => Bool) R τ :=
  embedStmt (Returning.layout (fun _ => [])) states labels stop q

theorem statement_frame (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (frame : J → List Bool) :
    statement states labels stop q = embedStmt (Returning.layout frame) states labels stop q := by
  unfold statement
  induction q with
  | push k f q ih => dsimp only [embedStmt]; rw [ih]; rfl
  | pop k f q ih => dsimp only [embedStmt]; rw [ih]; rfl
  | peek k f q ih => dsimp only [embedStmt]; rw [ih]; rfl
  | load f q ih => dsimp only [embedStmt]; rw [ih]
  | branch f a b ha hb => dsimp only [embedStmt]; rw [ha, hb]
  | goto f => rfl
  | halt => rfl

/-- Exact source execution, including the compiled return replacing source halt. -/
theorem run (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : K ⊕ J => Bool) R τ)
    (agree : ∀ label, target (labels label) = statement states labels stop (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (frame : J → List Bool) (n : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) :
    (fun p => p.bind (TM2.step target))^[n]
      (some (embedCfg (Returning.layout frame) states labels stop c)) =
      some (embedCfg (Returning.layout frame) states labels stop d) :=
  embed_run (Returning.layout frame) states labels stop source target
    (fun label => (agree label).trans (statement_frame states labels stop (source label) frame)) c d n h

theorem statement_budget (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (statement (J := J) states labels stop q) = TM2Cost.budget q := embed_budget _ _ _ _ _

section AnyLayout
variable {Target : Type} [DecidableEq Target]

/-- Compiled syntax depends on selected finite stack keys, never on frame data. -/
theorem embedStmt_congr_key (a b : StackEmbedding K Target) (hk : a.key = b.key)
    (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    embedStmt a states labels stop q = embedStmt b states labels stop q := by
  induction q with
  | push k f q ih => simp only [embedStmt, hk, ih]
  | pop k f q ih => simp only [embedStmt, hk, ih]
  | peek k f q ih => simp only [embedStmt, hk, ih]
  | load f q ih => simp only [embedStmt, ih]
  | branch f x y hx hy => simp only [embedStmt, hx, hy]
  | goto f => rfl
  | halt => rfl

/-- A constant program layout may be verified against any compatible preserved
frame. This supports several disjoint source machines inside one finite controller. -/
theorem run_with_frame (base layout : StackEmbedding K Target) (hk : base.key = layout.key)
    (states : StateEmbedding σ τ) (labels : Λ → R) (stop : Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : Target => Bool) R τ)
    (agree : ∀ label, target (labels label) = embedStmt base states labels stop (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (n : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) :
    (fun p => p.bind (TM2.step target))^[n]
      (some (embedCfg layout states labels stop c)) = some (embedCfg layout states labels stop d) :=
  embed_run layout states labels stop source target
    (fun label => (agree label).trans (embedStmt_congr_key base layout hk states labels stop (source label))) c d n h
end AnyLayout

end Holant.Complexity.GraphPreprocessing.Call

namespace Holant.Complexity.GraphPreprocessing
open Turing StackProtocol
variable {K Λ τ : Type} [DecidableEq K]

/-- Order-preserving transfer onto an arbitrary destination suffix and caller frame. -/
theorem transfer_exact_frame (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
    (memory : τ) (frame : K → List Bool) (word suffix : List Bool) :
    RunsExactly step (cfg move memory (tapes3 frame src dst tmp word suffix []))
      (cfg next memory (tapes3 frame src dst tmp [] (word ++ suffix) [])) (2 * (word.length + 1)) := by
  have first := copy_move_exact src dst tmp hsd hst step move restore hm memory frame word suffix []
  simp only [List.append_nil] at first
  have last := Frame.restore_exact src dst tmp hdt step restore next hr memory frame [] suffix word.reverse
  simpa [Nat.two_mul] using first.trans last

end Holant.Complexity.GraphPreprocessing
