import Holant.Proofs.CountingMachines.StandardMachine.ReencodedWitness
import Holant.Proofs.CountingMachines.StandardMachine.Support.Cost

set_option backward.isDefEq.respectTransparency false
/-! Actual primitive and finite-symbol storage bounds for a constructed
finite verifier, including the heterogeneous recoding composition. The bound
is obtained from its real output run, never from encoded output length. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.VerifierResources
open Turing Computability Holant.Complexity
variable {α β Γ Δ : Type} [Fintype Γ] [Fintype Δ]
variable {ea : Encoding α Γ} {eb : Encoding β Δ} {f : α → β} (v : PolyTime ea eb f)

def machine : Support.BinaryMachine where
  core := v.tm
  alternate := v.tm.m
  split _ := false
  alphabets := v.finiteAlphabets

def capacityPolynomial : Polynomial ℕ := Polynomial.X +
  v.time * Polynomial.C (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget v.tm)
def primitivePolynomial : Polynomial ℕ := v.time * Polynomial.C (machine v).primitiveBudget
def bitsPolynomial : Polynomial ℕ := Polynomial.C (machine v).controlBits +
  capacityPolynomial v * Polynomial.C (machine v).symbolWidths

theorem prefix_exists (a : α) (j : ℕ) (hj : j ≤ (v.outputsFun a).steps) :
    ∃ next, (fun p => p.bind v.tm.step)^[j]
      (some (initList v.tm ((ea.encode a).map v.inputAlphabet.invFun))) = some next := by
  cases hp : (fun p => p.bind v.tm.step)^[j]
      (some (initList v.tm ((ea.encode a).map v.inputAlphabet.invFun))) with
  | some next => exact ⟨next,rfl⟩
  | none =>
      have hn : (fun p : Option v.tm.Cfg => p.bind v.tm.step)^[(v.outputsFun a).steps-j] none = none :=
        Function.iterate_fixed (f := fun p : Option v.tm.Cfg => p.bind v.tm.step) rfl _
      have h := (v.outputsFun a).evals_in_steps
      change (fun p => p.bind v.tm.step)^[(v.outputsFun a).steps]
          (some (initList v.tm ((ea.encode a).map v.inputAlphabet.invFun))) =
        some (haltList v.tm ((eb.encode (f a)).map v.outputAlphabet.invFun)) at h
      rw [show (v.outputsFun a).steps = ((v.outputsFun a).steps-j)+j by omega,
        Function.iterate_add_apply,hp,hn] at h
      cases h

theorem prefix_capacity (a : α) (j : ℕ) (next : v.tm.Cfg)
    (hj : j ≤ (v.outputsFun a).steps)
    (hr : (fun p => p.bind v.tm.step)^[j]
      (some (initList v.tm ((ea.encode a).map v.inputAlphabet.invFun))) = some next) :
    ∀ k, (next.stk k).length ≤ (capacityPolynomial v).eval (ea.encode a).length := by
  have hhold := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some v.tm j _ _ hr
  have htime := hj.trans (v.outputsFun a).steps_le_m
  have hmul := Nat.mul_le_mul_right
    (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget v.tm) htime
  intro k
  have h := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound v.tm
    ((ea.encode a).map v.inputAlphabet.invFun) j k
  rw [hhold] at h
  simp only [List.length_map] at h
  simpa only [capacityPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_C] using h.trans (Nat.add_le_add_left hmul _)

theorem prefix_primitive (a : α) (j : ℕ) (hj : j ≤ (v.outputsFun a).steps) :
    (machine v).primitiveCost j ([],initList v.tm ((ea.encode a).map v.inputAlphabet.invFun)) ≤
      (primitivePolynomial v).eval (ea.encode a).length := by
  have ht := hj.trans (v.outputsFun a).steps_le_m
  exact ((machine v).primitiveCost_le j _).trans
    (by simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_right (machine v).primitiveBudget ht)

theorem prefix_bits (a : α) (j : ℕ) (next : v.tm.Cfg)
    (hj : j ≤ (v.outputsFun a).steps)
    (hr : (fun p => p.bind v.tm.step)^[j]
      (some (initList v.tm ((ea.encode a).map v.inputAlphabet.invFun))) = some next) :
    (machine v).codedStorageBits next ≤ (bitsPolynomial v).eval (ea.encode a).length := by
  have h := ((machine v).codedStorageBits_le next).trans
    ((machine v).storageBits_le next _ (prefix_capacity v a j next hj hr))
  simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using h

/-- Every prefix of the actual generated verifier has the same original-input
polynomial bounds, including rejected witnesses and both recoding stages. -/
theorem actual_prefix (a : α) (j : ℕ) (hj : j ≤ (v.outputsFun a).steps) :
    ∃ next, (fun p => p.bind v.tm.step)^[j]
      (some (initList v.tm ((ea.encode a).map v.inputAlphabet.invFun))) = some next ∧
      (∀ k, (next.stk k).length ≤ (capacityPolynomial v).eval (ea.encode a).length) ∧
      (machine v).primitiveCost j ([],initList v.tm ((ea.encode a).map v.inputAlphabet.invFun)) ≤
        (primitivePolynomial v).eval (ea.encode a).length ∧
      (machine v).codedStorageBits next ≤ (bitsPolynomial v).eval (ea.encode a).length := by
  obtain ⟨next,hr⟩ := prefix_exists v a j hj
  exact ⟨next,hr,prefix_capacity v a j next hj hr,prefix_primitive v a j hj,prefix_bits v a j next hj hr⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.VerifierResources
