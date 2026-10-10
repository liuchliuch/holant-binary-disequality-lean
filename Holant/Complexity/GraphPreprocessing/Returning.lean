import Holant.Complexity.BinaryCompose.Embed

/-! Compile several distinct exits of a finite source program into caller return
labels while preserving its Boolean-stack frame. Active execution prefixes are
simulated exactly, so found/missing/malformed exits can return separately without
turning any whole-word operation into a machine instruction. -/
namespace Holant.Complexity.GraphPreprocessing.Returning
open Turing BinaryCompose
variable {K J Λ R σ : Type} [DecidableEq K] [DecidableEq J]

def layout (frame : J → List Bool) : StackEmbedding K (K ⊕ J) where
  key := Sum.inl
  lift source := Sum.elim source frame
  lookup _ _ := rfl
  update source k word := MachineFrame.update_left source frame k word

def state : StateEmbedding σ σ where
  put := id
  get := id
  get_put _ := rfl

def stmt (ret : R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ :=
  embedStmt (layout (fun _ => [])) state Sum.inl (some (.inr ret)) q

/-- Every source label may have its own terminal return destination. -/
def program (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ret : Λ → R)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ) :
    (Λ ⊕ R) → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ
  | .inl label => stmt (ret label) (source label)
  | .inr label => outside label

def cfg (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (frame : J → List Bool) :
    TM2.Cfg (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ where
  l := c.l.map Sum.inl
  var := c.var
  stk := Sum.elim c.stk frame

private theorem stmt_frame (ret : R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (frame : J → List Bool) :
    stmt ret q = embedStmt (layout frame) state Sum.inl (some (.inr ret)) q := by
  unfold stmt
  induction q with
  | push k f q ih => dsimp only [embedStmt]; rw [ih]; rfl
  | pop k f q ih => dsimp only [embedStmt]; rw [ih]; rfl
  | peek k f q ih => dsimp only [embedStmt]; rw [ih]; rfl
  | load f q ih => dsimp only [embedStmt]; rw [ih]
  | branch f a b ha hb => dsimp only [embedStmt]; rw [ha, hb]
  | goto f => rfl
  | halt => rfl

private theorem embedCfg_active (ret : R) (c : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (frame : J → List Bool) (active : c.l.isSome) :
    embedCfg (layout frame) state Sum.inl (some (.inr ret)) c = cfg c frame := by
  rcases c with ⟨label, v, tapes⟩
  cases label with
  | none => simp at active
  | some label => rfl

/-- An active source result cannot have executed a halt, so its label is unchanged. -/
theorem step_active (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ret : Λ → R)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ)
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (frame : J → List Bool)
    (h : TM2.step source c = some d) (active : d.l.isSome) :
    TM2.step (program source ret outside) (cfg c frame) = some (cfg d frame) := by
  rcases c with ⟨label, v, tapes⟩
  cases label with
  | none => simp [TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (source label) v tapes = d := Option.some.inj h
    simp only [cfg, Option.map_some, TM2.step, program, stmt_frame (ret label) (source label) frame]
    change some (TM2.stepAux (embedStmt (layout frame) state Sum.inl (some (.inr (ret label))) (source label))
      (state.put v) ((layout frame).lift tapes)) = _
    rw [embed_stepAux, hd, embedCfg_active _ _ _ active]
    rfl

/-- Every execution ending at an active source label lifts exactly. -/
theorem run_active (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ret : Λ → R)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ)
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (frame : J → List Bool) (n : ℕ)
    (h : (fun x => x.bind (TM2.step source))^[n] (some c) = some d) (active : d.l.isSome) :
    (fun x => x.bind (TM2.step (program source ret outside)))^[n] (some (cfg c frame)) = some (cfg d frame) := by
  induction n generalizing d with
  | zero => cases Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun x => x.bind (TM2.step source))^[n] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : TM2.step source previous = some d := by simpa [hp] using h
      have ha : previous.l.isSome := by
        rcases previous with ⟨label, v, tapes⟩
        cases label with
        | none => simp [TM2.step] at hs
        | some label => rfl
      rw [Function.iterate_succ_apply', ih previous hp ha]
      exact step_active source ret outside previous d frame hs active

/-- The source exit's literal halt becomes its corresponding caller jump. -/
theorem return_step (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ret : Λ → R)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ)
    (label : Λ) (h : source label = .halt) (v : σ) (tapes : K → List Bool) (frame : J → List Bool) :
    TM2.step (program source ret outside) (cfg ⟨some label, v, tapes⟩ frame) =
      some ⟨some (.inr (ret label)), v, Sum.elim tapes frame⟩ := by
  simp [TM2.step, cfg, program, h, stmt, embedStmt, TM2.stepAux, state]

/-- Structural compilation preserves the primitive budget, including return jumps. -/
theorem statement_budget (ret : R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (stmt (J := J) ret q) = TM2Cost.budget q :=
  embed_budget _ _ _ _ _

end Holant.Complexity.GraphPreprocessing.Returning
