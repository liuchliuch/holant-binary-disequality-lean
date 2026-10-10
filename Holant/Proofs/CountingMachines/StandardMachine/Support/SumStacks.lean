import Holant.Proofs.CountingMachines.StandardMachine.Support.Foundation
import Holant.Complexity.BinaryCompose.Embed

set_option backward.isDefEq.respectTransparency false
/-! Reference adaptation. See the task validation reports. Literal finite programs for physical preparation,
framed input scanning, exactly W binary choices, original-input transfer and the
unchanged heterogeneous verifier. No whole-list operation is a machine opcode.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing StackProtocol

namespace SumStacks
variable {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J] (Γ : J → Type)
abbrev Alphabet : K ⊕ J → Type
  | .inl _ => Bool
  | .inr j => Γ j
def merge (left : K → List Bool) (right : ∀ j, List (Γ j)) :
    ∀ k : K ⊕ J, List (Alphabet Γ k)
  | .inl k => left k
  | .inr j => right j

theorem update_left (left : K → List Bool) (right : ∀ j, List (Γ j))
    (k : K) (word : List Bool) :
    Function.update (merge Γ left right) (.inl k) word =
      merge Γ (Function.update left k word) right := by
  funext key
  cases key with
  | inl j => by_cases h : j = k <;> simp [merge, h]
  | inr j => simp [merge]

theorem update_right (left : K → List Bool) (right : ∀ j, List (Γ j))
    (k : J) (word : List (Γ k)) :
    Function.update (merge Γ left right) (.inr k) word =
      merge Γ left (Function.update right k word) := by
  funext key
  cases key with
  | inl j => simp [merge]
  | inr j => by_cases h : j = k <;> simp [merge, h]

def leftStmt : TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (Alphabet (K := K) Γ) Λ σ
  | .push k f q => .push (.inl k) f (leftStmt q)
  | .pop k f q => .pop (.inl k) f (leftStmt q)
  | .peek k f q => .peek (.inl k) f (leftStmt q)
  | .load f q => .load f (leftStmt q)
  | .branch f q r => .branch f (leftStmt q) (leftStmt r)
  | .goto f => .goto f
  | .halt => .halt

def leftCfg (right : ∀ j, List (Γ j)) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (Alphabet (K := K) Γ) Λ σ := ⟨c.l,c.var,merge Γ c.stk right⟩

theorem left_stepAux (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ)
    (left : K → List Bool) (right : ∀ j, List (Γ j)) :
    TM2.stepAux (leftStmt Γ q) v (merge Γ left right) =
      leftCfg Γ right (TM2.stepAux q v left) := by
  induction q generalizing v left with
  | push k f q ih => simpa only [leftStmt,TM2.stepAux,merge,update_left] using ih v _
  | pop k f q ih => simpa only [leftStmt,TM2.stepAux,merge,update_left] using ih _ _
  | peek k f q ih => simpa only [leftStmt,TM2.stepAux,merge] using ih _ left
  | load f q ih => exact ih _ left
  | branch f q r hq hr => cases h : f v <;> simp [leftStmt,TM2.stepAux,h,hq,hr]
  | goto f => rfl
  | halt => rfl

def rightStmt (states : StateEmbedding σ τ) (labels : Λ → R) :
    TM2.Stmt Γ Λ σ → TM2.Stmt (Alphabet (K := K) Γ) R τ
  | .push k f q => .push (.inr k) (fun v => f (states.get v)) (rightStmt states labels q)
  | .pop k f q => .pop (.inr k) (fun v b => states.put (f (states.get v) b))
      (rightStmt states labels q)
  | .peek k f q => .peek (.inr k) (fun v b => states.put (f (states.get v) b))
      (rightStmt states labels q)
  | .load f q => .load (fun v => states.put (f (states.get v))) (rightStmt states labels q)
  | .branch f q r => .branch (fun v => f (states.get v))
      (rightStmt states labels q) (rightStmt states labels r)
  | .goto f => .goto (fun v => labels (f (states.get v)))
  | .halt => .halt

def rightCfg (states : StateEmbedding σ τ) (labels : Λ → R) (left : K → List Bool)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg (Alphabet (K := K) Γ) R τ :=
  ⟨c.l.map labels,states.put c.var,merge Γ left c.stk⟩

theorem right_stepAux (states : StateEmbedding σ τ) (labels : Λ → R)
    (q : TM2.Stmt Γ Λ σ) (v : σ) (left : K → List Bool) (right : ∀ j, List (Γ j)) :
    TM2.stepAux (rightStmt Γ states labels q) (states.put v) (merge Γ left right) =
      rightCfg Γ states labels left (TM2.stepAux q v right) := by
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
  | halt => rfl
end SumStacks

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
