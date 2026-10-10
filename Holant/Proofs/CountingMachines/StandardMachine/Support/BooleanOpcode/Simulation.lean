import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Compiler

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Exact edge and trace transport on coded tape states.
Only original split labels consume bits; Boolean decoder branches are finite
deterministic control tests. This is not yet a whole raw-input constructor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Compiler
open Turing Computability Holant.Complexity
variable (m : BinaryMachine)

theorem step_cfg (token : Option Bool) (c : m.Config) :
    (machine m).step token (cfg m c) = (m.step token c).map (cfg m) := by
  cases hl : c.l with
  | none => cases token <;> simp [BinaryMachine.step,cfg,hl]
  | some l =>
    cases token with
    | none => cases hs : m.split l <;>
        simp [BinaryMachine.step,machine,computer,cfg,hl,hs,Block.clear] <;>
        first
        | simpa only [cfg,Block.clear] using statement_stepAux m (m.core.m l) c.var c.stk
        | simpa only [cfg,Block.clear] using statement_stepAux m (m.alternate l) c.var c.stk
    | some b => cases b <;> cases hs : m.split l <;>
        simp [BinaryMachine.step,machine,computer,cfg,hl,hs,Block.clear] <;>
        first
        | simpa only [cfg,Block.clear] using statement_stepAux m (m.core.m l) c.var c.stk
        | simpa only [cfg,Block.clear] using statement_stepAux m (m.alternate l) c.var c.stk

theorem trace_recover (tokens : List (Option Bool)) (c : m.Config)
    (d : (machine m).Config) :
    (machine m).TraceValid tokens (cfg m c) d ↔
      ∃ original, m.TraceValid tokens c original ∧ d = cfg m original := by
  induction tokens generalizing c with
  | nil =>
    constructor
    · intro h; exact ⟨c,rfl,h.symm⟩
    · rintro ⟨original,ho,hd⟩
      change c = original at ho
      subst original
      exact hd.symm
  | cons token tokens ih =>
    constructor
    · rintro ⟨next,hs,ht⟩
      rw [step_cfg] at hs
      cases ho : m.step token c with
      | none => simp [ho] at hs
      | some sourceNext =>
        have hn : cfg m sourceNext = next := Option.some.inj (by simpa [ho] using hs)
        subst next
        obtain ⟨original,hr,hd⟩ := (ih sourceNext).mp ht
        exact ⟨original,⟨sourceNext,ho,hr⟩,hd⟩
    · rintro ⟨original,⟨sourceNext,hs,ht⟩,hd⟩
      refine ⟨cfg m sourceNext,?_,(ih sourceNext).mpr ⟨original,ht,hd⟩⟩
      rw [step_cfg,hs]
      rfl

theorem trace_cfg_iff (tokens : List (Option Bool)) (c d : m.Config) :
    (machine m).TraceValid tokens (cfg m c) (cfg m d) ↔ m.TraceValid tokens c d := by
  rw [trace_recover]
  constructor
  · rintro ⟨original,ht,hd⟩
    have ho : d = original := cfg_injective m hd
    subst original
    exact ht
  · intro ht; exact ⟨d,ht,rfl⟩

abbrev Path (n : ℕ) (c d : m.Config) :=
  {tokens : Fin n → Option Bool // m.TraceValid (List.ofFn tokens) c d}
abbrev CodedPath (n : ℕ) (c d : m.Config) :=
  {tokens : Fin n → Option Bool // (machine m).TraceValid (List.ofFn tokens) (cfg m c) (cfg m d)}

noncomputable instance pathFintype (n : ℕ) (c d : m.Config) : Fintype (Path m n c d) := by
  classical
  unfold Path
  infer_instance
noncomputable instance codedPathFintype (n : ℕ) (c d : m.Config) : Fintype (CodedPath m n c d) := by
  classical
  unfold CodedPath
  infer_instance

/-- Both maps retain every token, including unique held-halt none padding. -/
def pathsEquiv (n : ℕ) (c d : m.Config) : Path m n c d ≃ CodedPath m n c d where
  toFun p := ⟨p.val,(trace_cfg_iff m _ c d).mpr p.property⟩
  invFun p := ⟨p.val,(trace_cfg_iff m _ c d).mp p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem paths_count (n : ℕ) (c d : m.Config) :
    Fintype.card (Path m n c d) = Fintype.card (CodedPath m n c d) :=
  Fintype.card_congr (pathsEquiv m n c d)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Compiler
