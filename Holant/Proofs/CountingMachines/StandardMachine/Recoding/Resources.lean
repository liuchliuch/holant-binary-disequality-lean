import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Source
import Holant.Proofs.CountingMachines.StandardMachine.Support.Cost

set_option backward.isDefEq.respectTransparency false
/-! Primitive costs and actual-prefix stack storage of the literal recoder.
The instrumentation is proof-only and follows the same finite instructions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding
open Turing Computability Holant.Complexity
open Support
variable {Γ Δ : Type} [Fintype Γ] [Fintype Δ]

theorem pushWord_budget (word : List Δ) (next : Stmt Γ Δ) :
    HeterogeneousCost.budget (pushWord word next) = word.length + HeterogeneousCost.budget next := by
  induction word generalizing next with
  | nil => simp [pushWord]
  | cons bit rest ih => simp [pushWord,ih,HeterogeneousCost.budget,Nat.add_assoc,Nat.add_comm]

theorem program_budget (code : Γ → List Δ) (label : Label Γ) :
    HeterogeneousCost.budget (program code label) ≤ width code + 4 := by
  cases label with
  | inl b => cases b <;> simp [program,HeterogeneousCost.budget]
  | inr p =>
      rcases p with ⟨b,a⟩
      cases b with
      | false => simp [program,HeterogeneousCost.budget]
      | true =>
          have h := code_length_le code a
          simp only [program,pushWord_budget,HeterogeneousCost.budget]
          omega

def transitionCost (code : Γ → List Δ) (c : Cfg Γ Δ) : ℕ :=
  c.l.elim 0 (fun l => (HeterogeneousCost.execute (program code l) c.var c.stk).1)

theorem transitionCost_le (code : Γ → List Δ) (c : Cfg Γ Δ) :
    transitionCost code c ≤ width code + 4 := by
  cases hl : c.l with
  | none => simp [transitionCost,hl]
  | some l =>
      simpa only [transitionCost,hl,Option.elim_some] using
        (HeterogeneousCost.cost_le (program code l) c.var c.stk).trans (program_budget code l)

/-- Accumulated executed primitive instructions of precisely the same run. -/
def primitiveCost (code : Γ → List Δ) : ℕ → Option (Cfg Γ Δ) → ℕ
  | 0, _ => 0
  | n+1, c => ((c.map (transitionCost code)).getD 0) +
      primitiveCost code n (c.bind (machine code).step)

theorem primitiveCost_le (code : Γ → List Δ) (n : ℕ) (c : Option (Cfg Γ Δ)) :
    primitiveCost code n c ≤ n * (width code + 4) := by
  induction n generalizing c with
  | zero => simp [primitiveCost]
  | succ n ih =>
      have hc : (c.map (transitionCost code)).getD 0 ≤ width code + 4 := by
        cases c with
        | none => simp
        | some c => exact transitionCost_le code c
      have hr := ih (c.bind (machine code).step)
      simp only [primitiveCost,Nat.succ_mul]
      omega

def primitivePolynomial (code : Γ → List Δ) : Polynomial ℕ :=
  (Polynomial.C 4 * Polynomial.X + Polynomial.C 2) * Polynomial.C (width code + 4)

theorem primitive_time (code : Γ → List Δ) (word : List Γ) :
    primitiveCost code (4*word.length+2) (some (initList (machine code) word)) ≤
      (primitivePolynomial code).eval word.length := by
  simpa [primitivePolynomial] using primitiveCost_le code (4*word.length+2) (some (initList (machine code) word))

/-- Physical prefix storage follows actual stack operations, including the
temporary reversed input. The bound is independent of any output-size guess. -/
theorem prefix_stack (code : Γ → List Δ) (word : List Γ) (j : ℕ) (c : Cfg Γ Δ)
    (h : run code j (some (initList (machine code) word)) = some c) (k : Key) :
    (c.stk k).length ≤ word.length + j * Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (machine code) := by
  have he := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some
    (machine code) j _ c h
  have hs := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (machine code) word j k
  simpa only [he] using hs

def stackPolynomial (code : Γ → List Δ) : Polynomial ℕ :=
  Polynomial.X + (Polynomial.C 4 * Polynomial.X + Polynomial.C 2) *
    Polynomial.C (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (machine code))

theorem prefix_stack_polynomial (code : Γ → List Δ) (word : List Γ) (j : ℕ) (c : Cfg Γ Δ)
    (hj : j ≤ 4*word.length+2)
    (h : run code j (some (initList (machine code) word)) = some c) (k : Key) :
    (c.stk k).length ≤ (stackPolynomial code).eval word.length := by
  have hs := prefix_stack code word j c h k
  have hm := Nat.mul_le_mul_right
    (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (machine code)) hj
  simp only [stackPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Recoding
