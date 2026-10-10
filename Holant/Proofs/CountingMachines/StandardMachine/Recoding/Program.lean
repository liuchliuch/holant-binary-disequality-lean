import Holant.Complexity.Encoding
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
/-! Literal finite-table symbol-to-word recoding. The source alphabet may be
empty. Two input-alphabet stacks reverse the source; finite emitter labels
prepend fixed target words using actual push syntax. No instruction acts on an
unbounded list, and the only register is one optional source symbol. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding
open Turing Computability Holant.Complexity

abbrev Key := Bool ⊕ Unit
abbrev Alphabet (Γ Δ : Type) : Key → Type
  | .inl _ => Γ
  | .inr _ => Δ
abbrev Label (Γ : Type) := Bool ⊕ (Bool × Γ)
abbrev Stmt (Γ Δ : Type) := TM2.Stmt (Alphabet Γ Δ) (Label Γ) (Option Γ)
abbrev Cfg (Γ Δ : Type) := TM2.Cfg (Alphabet Γ Δ) (Label Γ) (Option Γ)

variable {Γ Δ : Type}

/-- A fixed output word is compiled recursively to finite push syntax. -/
def pushWord : List Δ → Stmt Γ Δ → Stmt Γ Δ
  | [], next => next
  | bit :: rest, next => pushWord rest (.push (.inr ()) (fun _ => bit) next)

theorem pushWord_eval (word : List Δ) (next : Stmt Γ Δ) (state : Option Γ)
    (tapes : ∀ k, List (Alphabet Γ Δ k)) :
    TM2.stepAux (pushWord word next) state tapes =
      TM2.stepAux next state (Function.update tapes (.inr ()) (word ++ tapes (.inr ()))) := by
  induction word generalizing next with
  | nil => simp [pushWord]
  | cons bit rest ih =>
      rw [pushWord,ih]
      simp [TM2.stepAux,Function.update_idem]

def program (code : Γ → List Δ) : Label Γ → Stmt Γ Δ
  | .inl false =>
      .pop (.inl false) (fun _ a => a)
        (.goto (fun a => a.elim (.inl true) (fun x => .inr (false,x))))
  | .inl true =>
      .pop (.inl true) (fun _ a => a)
        (.branch Option.isSome
          (.goto (fun a => a.elim (.inl true) (fun x => .inr (true,x))))
          (.load (fun _ => none) .halt))
  | .inr (false,a) =>
      .push (.inl true) (fun _ => a)
        (.load (fun _ => none) (.goto (fun _ => .inl false)))
  | .inr (true,a) =>
      pushWord (code a) (.load (fun _ => none) (.goto (fun _ => .inl true)))

def tapes (source reverse : List Γ) (output : List Δ) : ∀ k, List (Alphabet Γ Δ k)
  | .inl false => source
  | .inl true => reverse
  | .inr () => output

def cfg (label : Label Γ) (state : Option Γ) (source reverse : List Γ) (output : List Δ) : Cfg Γ Δ :=
  ⟨some label,state,tapes source reverse output⟩

variable [Fintype Γ] [Fintype Δ]

abbrev machine (code : Γ → List Δ) : FinTM2 where
  K := Key
  k₀ := .inl false
  k₁ := .inr ()
  Γ := Alphabet Γ Δ
  Λ := Label Γ
  main := .inl false
  σ := Option Γ
  initialState := none
  m := program code

theorem scan_cons (code : Γ → List Δ) (a : Γ) (source reverse : List Γ) (out : List Δ) :
    (machine code).step (cfg (.inl false) none (a :: source) reverse out) =
      some (cfg (.inr (false,a)) (some a) source reverse out) := by
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,tapes]
  try simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

theorem scan_nil (code : Γ → List Δ) (reverse : List Γ) (out : List Δ) :
    (machine code).step (cfg (.inl false) none [] reverse out) =
      some (cfg (.inl true) none [] reverse out) := by
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,tapes]
  try simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

theorem reverse_push (code : Γ → List Δ) (a : Γ) (source reverse : List Γ) (out : List Δ) :
    (machine code).step (cfg (.inr (false,a)) (some a) source reverse out) =
      some (cfg (.inl false) none source (a :: reverse) out) := by
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,tapes]
  try simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

theorem emit_cons (code : Γ → List Δ) (a : Γ) (reverse : List Γ) (out : List Δ) :
    (machine code).step (cfg (.inl true) none [] (a :: reverse) out) =
      some (cfg (.inr (true,a)) (some a) [] reverse out) := by
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,tapes]
  try simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

theorem emit_push (code : Γ → List Δ) (a : Γ) (reverse : List Γ) (out : List Δ) :
    (machine code).step (cfg (.inr (true,a)) (some a) [] reverse out) =
      some (cfg (.inl true) none [] reverse (code a ++ out)) := by
  change some (TM2.stepAux (pushWord (code a) _) _ _) = _
  rw [pushWord_eval]
  dsimp [TM2.stepAux,cfg,tapes]
  try simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

theorem emit_nil (code : Γ → List Δ) (out : List Δ) :
    (machine code).step (cfg (.inl true) none [] [] out) =
      some (haltList (machine code) out) := by
  dsimp [FinTM2.step,TM2.step,machine,program,cfg,TM2.stepAux,tapes,haltList]
  try simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

theorem init_eq (code : Γ → List Δ) (word : List Γ) :
    initList (machine code) word = cfg (.inl false) none word [] [] := by
  dsimp [initList,machine,cfg]
  congr 1
  funext k
  rcases k with b | u
  · cases b <;> rfl
  · cases u; rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding
