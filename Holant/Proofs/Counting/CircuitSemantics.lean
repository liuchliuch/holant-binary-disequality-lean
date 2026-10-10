import Holant.Proofs.Counting.RawCompiler
import Holant.OrdinaryNetwork
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Contraction of all physically allocated circuit edges

Technical replay of the accepted CountingBridge local contraction proof under the original public circuit namespace. Validation is recorded separately.

A NAND allocates five edges, not merely one logical output bit. This file sums
over all five and proves the two copy vertices introduce no multiplicity or
scalar. The fragment semantics is then compared with literal emitted row weights.
-/

namespace Holant.LocalDrafts.CountingHardness.CircuitSemantics

open Holant Holant.Complexity RawCompiler
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype

def blockEquiv (a b : ℕ) :
    (Fin (a + b) → Bool) ≃ ((Fin a → Bool) × (Fin b → Bool)) where
  toFun z := (fun i => z (Fin.castAdd b i), fun i => z (Fin.natAdd a i))
  invFun p := Fin.addCases p.1 p.2
  left_inv z := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp

def consEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun z := (z 0, Fin.tail z)
  invFun p := Fin.cons p.1 p.2
  left_inv z := Fin.cons_self_tail z
  right_inv p := by simp

variable {K : Type*} [CommSemiring K]

theorem sum_block (a b : ℕ) (f : (Fin (a + b) → Bool) → K) :
    (∑ z, f z) = ∑ x : Fin a → Bool, ∑ y : Fin b → Bool, f (Fin.addCases x y) := by
  rw [← (blockEquiv a b).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

theorem sum_cons (n : ℕ) (f : (Fin (n + 1) → Bool) → K) :
    (∑ z, f z) = ∑ x : Bool, ∑ y : Fin n → Bool, f (Fin.cons x y) := by
  rw [← (consEquiv n).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

def nandWeight {n : ℕ} (x : Fin n → Bool) (a b : Fin n) (p : Fin 5 → Bool) : K :=
  let x₁ := Function.update x a (p 0)
  GateAlphabet.copy ![x a, p 0, p 1] *
    GateAlphabet.copy ![x₁ b, p 2, p 3] * GateAlphabet.nand ![p 1, p 3, p 4]

def nandNext {n : ℕ} (x : Fin n → Bool) (a b : Fin n) (p : Fin 5 → Bool) :
    Fin (n + 1) → Bool :=
  Fin.cons (p 4) (Function.update (Function.update x a (p 0)) b (p 2))

/-- The literal five fresh edge choices reduce to exactly one output and the
unchanged register values. This also covers `a = b`. -/
theorem nand_contract {n : ℕ} (x : Fin n → Bool) (a b : Fin n)
    (f : (Fin (n + 1) → Bool) → K) :
    (∑ p : Fin 5 → Bool, nandWeight x a b p * f (nandNext x a b p)) =
      f (Fin.cons (!(x a && x b)) x) := by
  have ha : Function.update x a (x a) = x := Function.update_eq_self a x
  have hb : Function.update x b (x b) = x := Function.update_eq_self b x
  simp only [sum_cons]
  change (∑ p₀ : Bool, ∑ p₁ : Bool, ∑ p₂ : Bool, ∑ p₃ : Bool, ∑ p₄ : Bool,
    ∑ _ : Fin 0 → Bool,
      (GateAlphabet.copy ![x a, p₀, p₁] *
        GateAlphabet.copy ![(Function.update x a p₀) b, p₂, p₃] *
        GateAlphabet.nand ![p₁, p₃, p₄]) *
        f (Fin.cons p₄ (Function.update (Function.update x a p₀) b p₂))) = _
  simp only [Fintype.sum_unique, Fintype.sum_bool]
  cases hxa : x a <;> cases hxb : x b
  all_goals
    simp only [hxa] at ha
    simp only [hxb] at hb
    simp [GateAlphabet.copy, GateAlphabet.nand,
      hxa, hxb, ha, hb, -Fin.cons_update]

/-- A weight for precisely the fresh edge block in `RawCompiler.rows`. -/
def weight {n : ℕ} (c : Circuit n) (x : Fin n → Bool)
    (z : Fin (freshEdges c) → Bool) : K :=
  match c with
  | .output out => if x out then 1 else 0
  | .constant b c =>
    let p := (blockEquiv 1 (freshEdges c)) z
    GateAlphabet.pin b ![p.1 0] * weight c (Fin.cons (p.1 0) x) p.2
  | .nand a b c =>
    let p := (blockEquiv 5 (freshEdges c)) z
    nandWeight x a b p.1 * weight c (nandNext x a b p.1) p.2

theorem sum_weight {n : ℕ} (c : Circuit n) (x : Fin n → Bool) :
    (∑ z : Fin (freshEdges c) → Bool, weight c x z) = if c.eval x then 1 else (0 : K) := by
  induction c with
  | output out => simp [weight, freshEdges, Circuit.eval]
  | constant b c ih =>
    change (∑ z : Fin (1 + freshEdges c) → Bool, _) = _
    rw [sum_block]
    simp only [weight, blockEquiv, Equiv.coe_fn_mk, Fin.addCases_left, Fin.addCases_right]
    simp_rw [← Finset.mul_sum, ih]
    rw [sum_cons]
    simpa [Circuit.eval] using
      (GateAlphabet.pin_contract b (fun v => if c.eval (Fin.cons v x) then 1 else (0 : K)))
  | nand a b c ih =>
    change (∑ z : Fin (5 + freshEdges c) → Bool, _) = _
    rw [sum_block]
    simp only [weight, blockEquiv, Equiv.coe_fn_mk, Fin.addCases_left, Fin.addCases_right]
    simp_rw [← Finset.mul_sum, ih]
    exact nand_contract x a b (fun next => if c.eval next then 1 else (0 : K))

/-- Literal row evaluation with ordered ports. The default is irrelevant on
validated rows and is never a substitute for a valid-input proof. -/
def rowWeight (r : RawVertex) (ρ : ℕ → Bool) : K :=
  let x := fun i => ρ (r.2.getD i (0, false)).1
  match r.1 with
  | 0 => 1
  | 1 => GateAlphabet.pin false ![x 0]
  | 2 => GateAlphabet.pin true ![x 0]
  | 3 => GateAlphabet.copy ![x 0, x 1, x 2]
  | 4 => GateAlphabet.nand ![x 0, x 1, x 2]
  | _ => 0

def rowsWeight (rs : List RawVertex) (ρ : ℕ → Bool) : K := (rs.map (rowWeight · ρ)).prod

theorem read_update {n : ℕ} (env : Fin n → RawEndpoint) (a : Fin n)
    (q : RawEndpoint) (ρ : ℕ → Bool) :
    (fun i => ρ (Function.update env a q i).1) =
      Function.update (fun i => ρ (env i).1) a (ρ q.1) := by
  funext i
  by_cases hi : i = a <;> simp [hi]

theorem read_cons {n : ℕ} (env : Fin n → RawEndpoint) (p : RawEndpoint)
    (ρ : ℕ → Bool) :
    (fun i => ρ (Fin.cons (α := fun _ => RawEndpoint) p env i).1) = Fin.cons (ρ p.1) (fun i => ρ (env i).1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Product of the actual emitted ordered rows, with actual absolute edge IDs.
No well-formedness or denotation equality is postulated as an input. -/
theorem rowsWeight_eq {n : ℕ} (c : Circuit n) (env : Fin n → RawEndpoint)
    (offset : ℕ) (ρ : ℕ → Bool) :
    rowsWeight (K := K) (rows c env offset) ρ =
      weight c (fun i => ρ (env i).1) (fun j => ρ (offset + j.val)) := by
  induction c generalizing offset with
  | output out =>
    simp only [rows, rowsWeight, List.map_ofFn, List.prod_ofFn]
    have he : ∀ i : Fin _,
        rowWeight (if i = out then 2 else 0, [env i]) ρ =
          if i = out then (if ρ (env out).1 then 1 else (0 : K)) else 1 := by
      intro i
      by_cases hi : i = out
      · subst i
        cases h : ρ (env out).1 <;> simp [rowWeight, GateAlphabet.pin, h]
      · simp [rowWeight, hi]
    simp [weight, he, Function.comp_def]
  | constant b c ih =>
    simp only [rows, rowsWeight, List.map_cons, List.prod_cons]
    change rowWeight _ ρ * rowsWeight (rows c _ _) ρ = _
    rw [ih]
    cases b <;> simp [weight, rowWeight, blockEquiv, read_cons, Nat.add_assoc]
  | nand a b c ih =>
    simp only [rows, rowsWeight, List.map_cons, List.prod_cons]
    change rowWeight _ ρ * (rowWeight _ ρ * (rowWeight _ ρ * rowsWeight (rows c _ _) ρ)) = _
    rw [ih]
    have hrb := congrFun (read_update env a (offset, true) ρ) b
    simp [weight, rowWeight, nandWeight, nandNext, blockEquiv, read_update, read_cons,
      hrb, Nat.add_assoc, mul_assoc, -Fin.cons_update]

end Holant.LocalDrafts.CountingHardness.CircuitSemantics
