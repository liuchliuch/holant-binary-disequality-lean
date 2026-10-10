import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Physical resource consequences for ordinary finite Boolean-stack machines.
The proofs begin with executed instructions and actual transition counts. They
never infer time from the size of a computed rational or serialized output. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.PrimitiveAccounting
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines

/-- Each finite statement's stack growth is paid by its actually executed
primitive instructions, rather than an arithmetic-unit-cost model. -/
theorem statement_growth {K Λ σ : Type} [Fintype K] [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (S : K → List Bool) :
    stackSize (TM2Cost.primitiveRun q v S).2.stk ≤
      stackSize S + (TM2Cost.primitiveRun q v S).1 := by
  induction q generalizing v S with
  | push k f q ih =>
    have hs := stackSize_update_le S k (f v :: S k) 1 (by simp)
    have hh := ih v (Function.update S k (f v :: S k))
    simp only [TM2Cost.primitiveRun]
    omega
  | pop k f q ih =>
    have hs := stackSize_update_le S k (S k).tail 0 (by simp)
    have hh := ih (f v (S k).head?) (Function.update S k (S k).tail)
    simp only [TM2Cost.primitiveRun]
    omega
  | peek k f q ih =>
    have hh := ih (f v (S k).head?) S
    simp only [TM2Cost.primitiveRun]
    omega
  | load f q ih =>
    have hh := ih (f v) S
    simp only [TM2Cost.primitiveRun]
    omega
  | branch f a b ha hb =>
    cases hv : f v
    · have hh := hb v S
      simp only [TM2Cost.primitiveRun, hv, Bool.false_eq_true, ite_false]
      omega
    · have hh := ha v S
      simp only [TM2Cost.primitiveRun, hv, ite_true]
      omega
  | goto f => simp [TM2Cost.primitiveRun]
  | halt => simp [TM2Cost.primitiveRun]

/-- Every prefix is charged, even if the selected final answer is very small. -/
theorem prefix_primitive_bound {A B : Type} {ea : Encoding A Bool}
    {eb : Encoding B Bool} {f : A → B} (w : Computes ea eb f) (a : A)
    (t : ℕ) (ht : t ≤ (w.outputs a).steps) :
    primitiveCost w.machine t (some (initList w.machine.computer (ea.encode a))) ≤
      (primitivePolynomial w).eval (ea.encode a).length := by
  apply (primitiveCost_le _ _ _).trans
  simpa only [primitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.mul_le_mul_right w.machine.primitiveBudget (ht.trans (w.outputs a).steps_le_m)

/-- The polynomial bounds the total of all finite stacks at every execution
prefix. Copies, arithmetic scratch, and serialized frames are all included. -/
theorem prefix_storage_bound {A B : Type} {ea : Encoding A Bool}
    {eb : Encoding B Bool} {f : A → B} (w : Computes ea eb f) (a : A)
    (t : ℕ) (ht : t ≤ (w.outputs a).steps) (c : w.machine.Config)
    (hc : (fun p => p.bind w.machine.computer.step)^[t]
      (some (initList w.machine.computer (ea.encode a))) = some c) :
    stackSize c.stk ≤ (Polynomial.X + primitivePolynomial w).eval (ea.encode a).length := by
  have hs := w.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  apply hs.trans
  have hr := Nat.mul_le_mul_right w.machine.primitiveBudget
    (ht.trans (w.outputs a).steps_le_m)
  simpa only [primitivePolynomial, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] using Nat.add_le_add_left hr (ea.encode a).length

end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.PrimitiveAccounting
