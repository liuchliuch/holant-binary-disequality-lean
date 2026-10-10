import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Encoding

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The actual original finite TM2 verifier is compiled
instruction by instruction. This Computes uses whole-pair block encoding;
it is not the SharpPWitness standard tagged Boolean input adapter. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness
open Turing Computability Holant.Complexity BinaryCompose
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open BooleanOpcode

namespace Verifier
variable (m : BinaryMachine)

theorem cfg_halt (out : List (m.core.Γ m.core.k₁)) :
    Compiler.cfg m (haltList m.core out) =
      haltList (Compiler.computer m) (Code.word m m.core.k₁ out) := by
  change (⟨_,_,_⟩ : (Compiler.machine m).Config) = ⟨_,_,_⟩
  congr 1
  funext k
  by_cases hk : k = m.core.k₁
  · subst k
    simp [Compiler.cfg,Code.tapes,haltList,Compiler.computer]
  · simp [Compiler.cfg,Code.tapes,Code.word,haltList,Compiler.computer,hk]

theorem core_step (c : m.core.Cfg) :
    (Compiler.computer m).step (Compiler.cfg m c) =
      (m.core.step c).map (Compiler.cfg m) := by
  rcases c with ⟨l,v,S⟩
  cases l <;> simp [FinTM2.step,TM2.step,Compiler.computer,Compiler.cfg,
    Compiler.statement_stepAux]

/-- Transport a real successful source run, retaining its exact transition
count. This is a consumer of the literal compiler theorem, not a simulation input. -/
theorem iterate_cfg (t : ℕ) (c d : m.core.Cfg)
    (h : (fun z : Option m.core.Cfg => z.bind m.core.step)^[t] (some c) = some d) :
    (fun z : Option (Compiler.computer m).Cfg => z.bind (Compiler.computer m).step)^[t]
      (some (Compiler.cfg m c)) = some (Compiler.cfg m d) := by
  induction t generalizing c with
  | zero =>
    have he : c = d := Option.some.inj h
    subst d
    rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases hs : m.core.step c with
    | none =>
        have hn : (fun z : Option m.core.Cfg => z.bind m.core.step)^[t] none = none :=
          Function.iterate_fixed (f := fun z : Option m.core.Cfg => z.bind m.core.step) rfl t
        simp only [Option.bind_some,hs,hn] at h
        cases h
    | some next =>
        have ht : (fun z : Option m.core.Cfg => z.bind m.core.step)^[t] (some next) =
            some d := by simpa only [Option.bind_some,hs] using h
        rw [Option.bind_some,core_step,hs,Option.map_some]
        exact ih next ht
end Verifier

variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)
local instance : Fintype w.verifier.tm.K := w.verifier.tm.kFin
local instance : Fintype w.verifier.tm.Λ := w.verifier.tm.ΛFin
local instance : Fintype w.verifier.tm.σ := w.verifier.tm.σFin

def compiledMachine : BinaryCompose.Machine where
  K := w.verifier.tm.K
  input := w.verifier.tm.k₀
  output := w.verifier.tm.k₁
  Label := w.verifier.tm.Λ
  main := w.verifier.tm.main
  State := Block.State (original w)
  finiteState := (Compiler.computer (original w)).σFin
  initial := Block.clear (original w) w.verifier.tm.initialState
  program l := Compiler.statement (original w) (w.verifier.tm.m l)

theorem pair_original_length_le (p : α × List Bool) :
    ((encodingProd ea (encodingList Bool)).encode p).length ≤
      ((pairEncoding w).encode p).length := by
  rw [encodingProd_length,pair_length]
  simpa only [Nat.one_mul,encodingList,codeWidth,id_eq] using Nat.mul_le_mul_right
    ((ea.encode p.1).length+p.2.length)
    (Nat.succ_le_of_lt (Code.width_pos (original w) (original w).core.k₀))

/-- Genuine clean Boolean-stack machine. Its input is the OLD pair's literal
fixed-block code, and its result is the OLD actual singleton result's code. -/
def compiledComputes : Computes (pairEncoding w) (outputEncoding w) w.accept where
  machine := compiledMachine w
  time := w.verifier.time
  outputs p := by
    have ho := w.verifier.outputsFun p
    change TM2OutputsInTime w.verifier.tm (payload w p)
      (some [resultSymbol w (w.accept p)])
      (w.verifier.time.eval ((encodingProd ea (encodingList Bool)).encode p).length) at ho
    have hr := Verifier.iterate_cfg (original w) ho.steps _ _ ho.evals_in_steps
    have hi : Compiler.cfg (original w) (initList w.verifier.tm (payload w p)) =
        initList (Compiler.computer (original w)) (Code.word (original w) (original w).core.k₀ (payload w p)) :=
      Compiler.cfg_init (original w) (payload w p)
    have hh : Compiler.cfg (original w) (haltList w.verifier.tm [resultSymbol w (w.accept p)]) =
        haltList (Compiler.computer (original w))
          (Code.word (original w) (original w).core.k₁ [resultSymbol w (w.accept p)]) :=
      Verifier.cfg_halt (original w) [resultSymbol w (w.accept p)]
    rw [hi,hh] at hr
    refine { steps := ho.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · convert hr using 1 <;> first | rfl | simp only [Code.word,List.flatMap_cons,List.flatMap_nil,List.append_nil,Option.map_some,outputEncoding]; rfl
    · exact ho.steps_le_m.trans (natPolynomial_eval_mono w.verifier.time
        (pair_original_length_le w p))

/-- Optional actual validation frontend, produced from the original input
payload and raw code. Neither prepared memory nor its correctness is caller input. -/
theorem initialize_step (p : α × List Bool) (log : List Bool) :
    (GeneralAlphabetInput.Program.machine (original w)).run
      (GeneralAlphabetInput.Program.steps (original w) (payload w p).length)
      (log,initList (GeneralAlphabetInput.Program.computer (original w))
        ((pairEncoding w).encode p)) =
      some (log,GeneralAlphabetInput.Program.readyCfg (original w)
        (Compiler.cfg (original w) (initList w.verifier.tm (payload w p)))) :=
  GeneralAlphabetInput.Program.prepare (original w) (payload w p) log

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness
