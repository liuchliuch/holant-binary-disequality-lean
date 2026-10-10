import Holant.Complexity.GraphPreprocessing.Call

/-! Returning finite subroutine simulation for arbitrary physical stack layouts
and distinct success/error exits. All translations are structural TM2 syntax. -/
namespace Holant.Complexity.GraphPreprocessing.Traversal.CallExits
open Turing BinaryCompose
variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]

theorem active_cfg (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (a b : Option R) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (active : c.l.isSome) :
    embedCfg layout states labels a c = embedCfg layout states labels b c := by
  rcases c with ⟨label,v,tapes⟩
  cases label with
  | none => simp at active
  | some label => rfl

theorem active_step (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (returns : Λ → Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R τ)
    (agree : ∀ label, target (labels label) = embedStmt layout states labels (returns label) (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (h : TM2.step source c = some d) (active : d.l.isSome) :
    TM2.step target (embedCfg layout states labels none c) =
      some (embedCfg layout states labels none d) := by
  rcases c with ⟨label,v,tapes⟩
  cases label with
  | none => simp [TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (source label) v tapes = d := Option.some.inj h
    change some (TM2.stepAux (target (labels label)) (states.put v) (layout.lift tapes)) = _
    rw [agree,embed_stepAux,hd,active_cfg layout states labels (returns label) none d active]

/-- An exact run to an active source exit cannot have executed its halt.
Different caller destinations therefore preserve every preceding transition. -/
theorem active_run (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (returns : Λ → Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R τ)
    (agree : ∀ label, target (labels label) = embedStmt layout states labels (returns label) (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (n : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) (active : d.l.isSome) :
    (fun p => p.bind (TM2.step target))^[n] (some (embedCfg layout states labels none c)) =
      some (embedCfg layout states labels none d) := by
  induction n generalizing d with
  | zero => cases Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step source))^[n] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : TM2.step source previous = some d := by simpa [hp] using h
      have ha : previous.l.isSome := by
        rcases previous with ⟨label,v,tapes⟩
        cases label with
        | none => simp [TM2.step] at hs
        | some label => rfl
      rw [Function.iterate_succ_apply',ih previous hp ha]
      exact active_step layout states labels returns source target agree previous d hs active

/-- The source terminal statement itself is one charged caller-return transition. -/
theorem return_step (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (returns : Λ → Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R τ)
    (agree : ∀ label, target (labels label) = embedStmt layout states labels (returns label) (source label))
    (label : Λ) (h : source label = .halt) (v : σ) (tapes : K → List Bool) :
    TM2.step target (embedCfg layout states labels none ⟨some label,v,tapes⟩) =
      some ⟨returns label,states.put v,layout.lift tapes⟩ := by
  change some (TM2.stepAux (target (labels label)) (states.put v) (layout.lift tapes)) = _
  rw [agree,h]
  cases returns label <;> rfl

/-- Fixed program keys can be checked once while the proof preserves the current
caller frame. Neither program construction nor execution inspects that frame. -/
theorem active_run_frame (base layout : StackEmbedding K J) (sameKeys : base.key = layout.key)
    (states : StateEmbedding σ τ) (labels : Λ → R) (returns : Λ → Option R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : R → TM2.Stmt (fun _ : J => Bool) R τ)
    (agree : ∀ label, target (labels label) = embedStmt base states labels (returns label) (source label))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (n : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[n] (some c) = some d) (active : d.l.isSome) :
    (fun p => p.bind (TM2.step target))^[n] (some (embedCfg layout states labels none c)) =
      some (embedCfg layout states labels none d) :=
  active_run layout states labels returns source target (fun label => (agree label).trans
    (Call.embedStmt_congr_key base layout sameKeys states labels (returns label) (source label))) c d n h active

end Holant.Complexity.GraphPreprocessing.Traversal.CallExits
