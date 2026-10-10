import Holant.Complexity.Encoding

/-! A fully finite TM2 that erases its input and writes one specified symbol.
The run takes exactly input length plus one transitions. -/

namespace Holant.Complexity

open Turing Computability
open Turing.TM2.Stmt

/-- One stack, one label, two internal states, and a finite alphabet. Each
transition pops one input symbol. After the empty stack is seen, write the answer. -/
abbrev constantSymbolComputer (Γ : Type) [Fintype Γ] (b : Γ) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Γ
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := pop () (fun _ x => x.isSome)
    (branch id
      (load (fun _ => false) (goto (fun _ => ())))
      (load (fun _ => false) (push () (fun _ => b) halt)))

@[simp] theorem constantSymbolComputer_step_cons {Γ : Type} [Fintype Γ]
    (b a : Γ) (l : List Γ) :
    (constantSymbolComputer Γ b).step (initList (constantSymbolComputer Γ b) (a :: l)) =
      some (initList (constantSymbolComputer Γ b) l) := by
  simp only [FinTM2.step, TM2.step, constantSymbolComputer, initList, TM2.stepAux]
  congr 2

@[simp] theorem constantSymbolComputer_step_nil {Γ : Type} [Fintype Γ]
    (b : Γ) :
    (constantSymbolComputer Γ b).step (initList (constantSymbolComputer Γ b) []) =
      some (haltList (constantSymbolComputer Γ b) [b]) := by
  simp only [FinTM2.step, TM2.step, constantSymbolComputer, initList, haltList, TM2.stepAux]
  congr 2

/-- Exact transition correctness; the bound is not an arbitrary cost annotation. -/
def constantSymbolComputer_outputs {Γ : Type} [Fintype Γ]
    (b : Γ) (l : List Γ) :
    TM2OutputsInTime (constantSymbolComputer Γ b) l (some [b]) (l.length + 1) := by
  induction l with
  | nil =>
    exact { steps := 1
            evals_in_steps := constantSymbolComputer_step_nil b
            steps_le_m := Nat.le_refl 1 }
  | cons a l ih =>
    exact StateTransition.EvalsToInTime.trans _ 1 (l.length + 1) _ _ _
      { steps := 1
        evals_in_steps := constantSymbolComputer_step_cons b a l
        steps_le_m := Nat.le_refl 1 } ih

/-- Constant Boolean predicates on faithfully encoded data have a concrete
linear-time machine. The output uses one tagged symbol. -/
noncomputable def constantBoolPolyTime {α Γ : Type} [Fintype Γ]
    (e : Encoding α (Γ ⊕ Bool)) (b : Bool) :
    PolyTime e (taggedBoolEncoding Γ) (fun _ => b) where
  tm := constantSymbolComputer (Γ ⊕ Bool) (Sum.inr b)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun a := by
    change TM2OutputsInTime (constantSymbolComputer (Γ ⊕ Bool) (Sum.inr b))
      (List.map id (e.encode a)) (some (List.map id [Sum.inr b]))
      ((Polynomial.X + 1).eval (e.encode a).length)
    rw [List.map_id, List.map_id]
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      using constantSymbolComputer_outputs (Sum.inr b) (e.encode a)
  finiteAlphabets _ := inferInstanceAs (Fintype (Γ ⊕ Bool))

end Holant.Complexity
