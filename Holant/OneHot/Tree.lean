import Holant.Signature
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-!
# Rooted-tree evaluation for one-hot signatures

The ordered tree evaluator core of manuscript Lemma 2.18. The semantics sums
Boolean endpoint choices, testing the at-most-one-occupied-port constraint at
each vertex. This module does not identify arbitrary network components with
these trees, handle unicyclic components, or establish bit complexity.
-/

namespace Holant.OneHot

universe u

mutual
/-- An ordered rooted tree with zero-word and parent-port coefficients. -/
inductive Tree (K : Type u) where
  | node (zero parent : K) (children : Forest K)
/-- Ordered child-port coefficient/subtree pairs. -/
inductive Forest (K : Type u) where
  | nil
  | cons (port : K) (child : Tree K) (rest : Forest K)
end

variable {K : Type*}

mutual
/-- One Boolean for every edge of the tree. -/
def Tree.Choice : Tree K → Type
  | .node _ _ ts => Forest.Choice ts
/-- `true` selects the endpoint at this forest's common parent; `false`
selects the endpoint at the child. -/
def Forest.Choice : Forest K → Type
  | .nil => Unit
  | .cons _ t ts => Bool × Tree.Choice t × Forest.Choice ts
end

mutual
@[instance_reducible] def Tree.choiceFintype : (t : Tree K) → Fintype t.Choice
  | .node _ _ ts => Forest.choiceFintype ts
@[instance_reducible] def Forest.choiceFintype : (ts : Forest K) → Fintype ts.Choice
  | .nil => inferInstanceAs (Fintype Unit)
  | .cons _ t ts =>
    letI := Tree.choiceFintype t
    letI := Forest.choiceFintype ts
    inferInstanceAs (Fintype (Bool × Tree.Choice t × Forest.Choice ts))
end

instance (t : Tree K) : Fintype t.Choice := t.choiceFintype
instance (ts : Forest K) : Fintype ts.Choice := ts.choiceFintype

/-- Number of selected endpoints at the forest's common parent. -/
def Forest.occupied : (ts : Forest K) → ts.Choice → ℕ
  | .nil, _ => 0
  | .cons _ _ ts, x => (if x.1 then 1 else 0) + ts.occupied x.2.2

variable [CommSemiring K]

/-- Product of coefficients of the parent endpoints selected by the choices. -/
def Forest.ports : (ts : Forest K) → ts.Choice → K
  | .nil, _ => 1
  | .cons p _ ts, x => (if x.1 then p else 1) * ts.ports x.2.2

mutual
/-- The product of local vertex weights for a specified endpoint configuration,
zero if any vertex has more than one occupied port. The boundary Boolean says
whether the parent edge selects this tree's root. -/
def Tree.weight : (t : Tree K) → Bool → t.Choice → K
  | .node a b ts, parent, x =>
    if (if parent then 1 else 0) + ts.occupied x ≤ 1 then
      (if parent then b else if ts.occupied x = 0 then a else ts.ports x) *
        ts.weight x
    else 0
/-- Product of the subtree weights for a complete forest configuration. -/
def Forest.weight : (ts : Forest K) → ts.Choice → K
  | .nil, _ => 1
  | .cons _ t ts, x => t.weight (!x.1) x.2.1 * ts.weight x.2.2
end

/-- Independent exhaustive endpoint-choice semantics. -/
def Tree.denote (t : Tree K) (parent : Bool) : K :=
  ∑ x : t.Choice, t.weight parent x

/-- The forest contribution with no selected endpoint at its common parent. -/
def Forest.emptyValue (ts : Forest K) : K :=
  ∑ x : ts.Choice, if ts.occupied x = 0 then ts.weight x else 0

/-- The forest contribution with exactly one selected endpoint at its parent. -/
def Forest.oneValue (ts : Forest K) : K :=
  ∑ x : ts.Choice, if ts.occupied x = 1 then ts.ports x * ts.weight x else 0

theorem Forest.ports_eq_one_of_occupied_zero (ts : Forest K) (x : ts.Choice)
    (h : ts.occupied x = 0) : ts.ports x = 1 := by
  cases ts with
  | nil => rfl
  | cons p t ts =>
    rcases x with ⟨b, y, z⟩
    cases b
    · simp only [Forest.occupied, Bool.false_eq_true, ↓reduceIte, zero_add] at h
      simp [Forest.ports, Forest.ports_eq_one_of_occupied_zero ts z h]
    · simp [Forest.occupied] at h

@[simp] theorem Tree.denote_true (a b : K) (ts : Forest K) :
    (Tree.node a b ts).denote true = b * ts.emptyValue := by
  unfold Tree.denote Forest.emptyValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ts.occupied x = 0
  · simp [Tree.weight, h]
  · have hn : ¬ 1 + ts.occupied x ≤ 1 := by omega
    simp [Tree.weight, h, hn]

@[simp] theorem Tree.denote_false (a b : K) (ts : Forest K) :
    (Tree.node a b ts).denote false = a * ts.emptyValue + ts.oneValue := by
  unfold Tree.denote Forest.emptyValue Forest.oneValue
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h0 : ts.occupied x = 0
  · simp [Tree.weight, h0]
  · by_cases h1 : ts.occupied x = 1
    · simp [Tree.weight, h1]
    · have hn : ¬ ts.occupied x ≤ 1 := by omega
      simp [Tree.weight, h0, h1, hn]

@[simp] theorem Forest.emptyValue_nil : (Forest.nil : Forest K).emptyValue = 1 := by
  change (∑ _ : Unit, (1 : K)) = 1
  simp

@[simp] theorem Forest.oneValue_nil : (Forest.nil : Forest K).oneValue = 0 := by
  simp [Forest.oneValue, Forest.occupied, Forest.Choice]

@[simp] theorem Forest.emptyValue_cons (p : K) (t : Tree K) (ts : Forest K) :
    (Forest.cons p t ts).emptyValue = t.denote true * ts.emptyValue := by
  change (∑ x : Bool × t.Choice × ts.Choice, _) = _
  simp only [Fintype.sum_prod_type,
    Fintype.sum_bool, Forest.occupied, Forest.weight, Bool.not_false,
    Bool.false_eq_true, ↓reduceIte, zero_add, Nat.add_eq_zero_iff, true_and,
    Nat.one_ne_zero, false_and, Finset.sum_const_zero]
  simp_rw [show ∀ (x : t.Choice) (y : ts.Choice),
    (if ts.occupied y = 0 then t.weight true x * ts.weight y else 0) =
    t.weight true x * (if ts.occupied y = 0 then ts.weight y else 0) by
      intros; split <;> simp_all]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

@[simp] theorem Forest.oneValue_cons (p : K) (t : Tree K) (ts : Forest K) :
    (Forest.cons p t ts).oneValue =
      p * t.denote false * ts.emptyValue + t.denote true * ts.oneValue := by
  have hp (b : Bool) (x : t.Choice) (y : ts.Choice) :
      (if (Forest.cons p t ts).occupied (b, x, y) = 1 then
        (Forest.cons p t ts).ports (b, x, y) *
          (Forest.cons p t ts).weight (b, x, y) else 0) =
      if b then p * t.weight false x * (if ts.occupied y = 0 then ts.weight y else 0)
      else t.weight true x * (if ts.occupied y = 1 then ts.ports y * ts.weight y else 0) := by
    cases b
    · by_cases h : ts.occupied y = 1 <;>
        simp [Forest.occupied, Forest.ports, Forest.weight, h, mul_left_comm]
    · by_cases h : ts.occupied y = 0
      · simp [Forest.occupied, Forest.ports, Forest.weight, h,
          ts.ports_eq_one_of_occupied_zero y h, mul_assoc]
      · simp [Forest.occupied, h]
  change (∑ x : Bool × t.Choice × ts.Choice, _) = _
  simp only [Fintype.sum_prod_type, hp, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp [Tree.denote, Forest.emptyValue, Forest.oneValue, ← Finset.mul_sum]

/-- The number of child edges at a root. -/
def Forest.length : Forest K → ℕ
  | .nil => 0
  | .cons _ _ ts => ts.length + 1

/-- Child data in port order: occupied-child value and parent-selection value. -/
def Forest.messages : (ts : Forest K) → Fin ts.length → K × K
  | .nil => Fin.elim0
  | .cons p t ts => Fin.cons (t.denote true, p * t.denote false) ts.messages

/-- The product of all occupied-child messages. -/
def messageProduct {n : ℕ} (m : Fin n → K × K) : K := ∏ i, (m i).1

/-- Explicit sum over the unique occupied child port. The factor at the chosen
child is omitted, using `1`; no nonzero assumptions or division are involved. -/
def messageSum {n : ℕ} (m : Fin n → K × K) : K :=
  ∑ i, (m i).2 * ∏ j, if j = i then 1 else (m j).1

@[simp] theorem messageProduct_cons {n : ℕ} (x : K × K) (m : Fin n → K × K) :
    messageProduct (Fin.cons x m) = x.1 * messageProduct m := by
  simp [messageProduct, Fin.prod_univ_succ]

@[simp] theorem messageSum_cons {n : ℕ} (x : K × K) (m : Fin n → K × K) :
    messageSum (Fin.cons x m) = x.2 * messageProduct m + x.1 * messageSum m := by
  simp only [messageSum, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _),
    ↓reduceIte, one_mul, Fin.succ_inj]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem Forest.emptyValue_eq_product (ts : Forest K) :
    ts.emptyValue = messageProduct ts.messages := by
  cases ts with
  | nil =>
    change (Forest.nil : Forest K).emptyValue = ∏ i : Fin 0, (Forest.nil.messages i).1
    simp
  | cons p t ts =>
    change (Forest.cons p t ts).emptyValue =
      messageProduct (Fin.cons (t.denote true, p * t.denote false) ts.messages)
    rw [Forest.emptyValue_cons, messageProduct_cons]
    rw [ts.emptyValue_eq_product]

theorem Forest.oneValue_eq_sum (ts : Forest K) :
    ts.oneValue = messageSum ts.messages := by
  cases ts with
  | nil =>
    change (Forest.nil : Forest K).oneValue =
      ∑ i : Fin 0, (Forest.nil.messages i).2 * ∏ j : Fin 0, _
    simp
  | cons p t ts =>
    change (Forest.cons p t ts).oneValue =
      messageSum (Fin.cons (t.denote true, p * t.denote false) ts.messages)
    rw [Forest.oneValue_cons, messageSum_cons]
    rw [ts.emptyValue_eq_product, ts.oneValue_eq_sum]

/-- The manuscript's `F_w(1)` equation, proved from endpoint-choice semantics. -/
theorem Tree.denote_true_product (a b : K) (ts : Forest K) :
    (Tree.node a b ts).denote true = b * ∏ i, (ts.messages i).1 := by
  rw [Tree.denote_true, ts.emptyValue_eq_product]
  rfl

/-- The manuscript's `F_w(0)` equation, with an explicit product over all other
children. It applies to the root as well as an unoccupied parent boundary. -/
theorem Tree.denote_false_sum (a b : K) (ts : Forest K) :
    (Tree.node a b ts).denote false =
      a * (∏ i, (ts.messages i).1) +
        ∑ i, (ts.messages i).2 * ∏ j, if j = i then 1 else (ts.messages j).1 := by
  rw [Tree.denote_false, ts.emptyValue_eq_product, ts.oneValue_eq_sum]
  rfl

mutual
/-- Division-free evaluator. The pair is `(F(0), F(1))`, both computed once. -/
def Tree.eval : Tree K → K × K
  | .node a b ts =>
    let s := ts.eval
    (a * s.1 + s.2, b * s.1)
/-- Linear child fold carrying the all-child product and the one-selection sum. -/
def Forest.eval : Forest K → K × K
  | .nil => (1, 0)
  | .cons p t ts =>
    let c := t.eval
    let s := ts.eval
    (c.2 * s.1, p * c.1 * s.1 + c.2 * s.2)
end

mutual
/-- The executable evaluator agrees with independent exhaustive semantics. -/
theorem Tree.eval_correct (t : Tree K) :
    t.eval = (t.denote false, t.denote true) := by
  cases t with
  | node a b ts =>
    simp only [Tree.eval, Forest.eval_correct, Tree.denote_false, Tree.denote_true]
theorem Forest.eval_correct (ts : Forest K) :
    ts.eval = (ts.emptyValue, ts.oneValue) := by
  cases ts with
  | nil => simp [Forest.eval]
  | cons p t ts =>
    simp only [Forest.eval, Tree.eval_correct, Forest.eval_correct,
      Forest.emptyValue_cons, Forest.oneValue_cons]
end

/-- A second statement of the child-fold specification exposes the exact
excluded-factor sum that it computes even in the presence of zero factors. -/
theorem Forest.eval_eq_product_sum (ts : Forest K) :
    ts.eval = (messageProduct ts.messages, messageSum ts.messages) := by
  rw [ts.eval_correct, ts.emptyValue_eq_product, ts.oneValue_eq_sum]

/-! ## Arithmetic instruction syntax and a checked linear operation count -/

/-- A finite arithmetic program with sharing through continuations. Each `add`
or `mul` constructor is one field/semiring operation. There is no timing oracle
or externally supplied operation-count annotation. -/
inductive Arithmetic (K : Type*) (A : Type*) where
  | pure (value : A)
  | add (left right : K) (next : K → Arithmetic K A)
  | mul (left right : K) (next : K → Arithmetic K A)

namespace Arithmetic

variable {A B : Type*}

def bind (p : Arithmetic K A) (f : A → Arithmetic K B) : Arithmetic K B :=
  match p with
  | .pure a => f a
  | .add x y next => .add x y (fun z => (next z).bind f)
  | .mul x y next => .mul x y (fun z => (next z).bind f)

instance : Monad (Arithmetic K) where
  pure := Arithmetic.pure
  bind := Arithmetic.bind

/-- Execute the arithmetic instructions and count precisely those instructions. -/
def run : Arithmetic K A → A × ℕ
  | .pure a => (a, 0)
  | .add x y next =>
    let r := (next (x + y)).run
    (r.1, r.2 + 1)
  | .mul x y next =>
    let r := (next (x * y)).run
    (r.1, r.2 + 1)

@[simp] theorem run_pure (a : A) : (Arithmetic.pure (K := K) a).run = (a, 0) := rfl

@[simp] theorem run_bind (p : Arithmetic K A) (f : A → Arithmetic K B) :
    (p.bind f).run =
      let r := p.run
      let s := (f r.1).run
      (s.1, r.2 + s.2) := by
  induction p with
  | pure a => simp [bind, run]
  | add x y next ih => simp [bind, run, ih, Nat.add_assoc, Nat.add_comm]
  | mul x y next ih => simp [bind, run, ih, Nat.add_assoc, Nat.add_comm]

/-- One explicit addition instruction. -/
def addOp (x y : K) : Arithmetic K K := .add x y .pure
/-- One explicit multiplication instruction. -/
def mulOp (x y : K) : Arithmetic K K := .mul x y .pure

@[simp] theorem run_addOp (x y : K) : (addOp x y).run = (x + y, 1) := rfl
@[simp] theorem run_mulOp (x y : K) : (mulOp x y).run = (x * y, 1) := rfl

end Arithmetic

mutual
/-- Compile the tree evaluator into actual addition and multiplication steps. -/
def Tree.program : Tree K → Arithmetic K (K × K)
  | .node a b ts => do
    let s ← ts.program
    let az ← Arithmetic.mulOp a s.1
    let free ← Arithmetic.addOp az s.2
    let occupied ← Arithmetic.mulOp b s.1
    pure (free, occupied)
/-- Each child result and accumulated suffix result is computed once and shared. -/
def Forest.program : Forest K → Arithmetic K (K × K)
  | .nil => pure (1, 0)
  | .cons p t ts => do
    let c ← t.program
    let s ← ts.program
    let prod ← Arithmetic.mulOp c.2 s.1
    let pc ← Arithmetic.mulOp p c.1
    let left ← Arithmetic.mulOp pc s.1
    let right ← Arithmetic.mulOp c.2 s.2
    let one ← Arithmetic.addOp left right
    pure (prod, one)
end

mutual
def Tree.vertices : Tree K → ℕ
  | .node _ _ ts => 1 + ts.vertices
def Forest.vertices : Forest K → ℕ
  | .nil => 0
  | .cons _ t ts => t.vertices + ts.vertices
end

mutual
def Tree.edges : Tree K → ℕ
  | .node _ _ ts => ts.edges
def Forest.edges : Forest K → ℕ
  | .nil => 0
  | .cons _ t ts => 1 + t.edges + ts.edges
end

mutual
/-- Exact operation count for the compiled syntax: three operations per vertex
and five per child edge. This is an arithmetic count, not a bit-time theorem. -/
theorem Tree.program_run (t : Tree K) :
    t.program.run = (t.eval, 3 * t.vertices + 5 * t.edges) := by
  cases t with
  | node a b ts =>
    simp only [Tree.program, bind, pure, Arithmetic.run_bind, Forest.program_run,
      Arithmetic.run_mulOp, Arithmetic.run_addOp, Arithmetic.run_pure,
      Tree.eval, Tree.vertices, Tree.edges]
    congr 1
    omega
theorem Forest.program_run (ts : Forest K) :
    ts.program.run = (ts.eval, 3 * ts.vertices + 5 * ts.edges) := by
  cases ts with
  | nil => rfl
  | cons p t ts =>
    simp only [Forest.program, bind, pure, Arithmetic.run_bind, Tree.program_run,
      Forest.program_run, Arithmetic.run_mulOp, Arithmetic.run_addOp,
      Arithmetic.run_pure, Forest.eval, Forest.vertices, Forest.edges]
    congr 1
    omega
end

/-- End-to-end specification of the explicit arithmetic program. -/
theorem Tree.program_spec (t : Tree K) :
    t.program.run =
      ((t.denote false, t.denote true), 3 * t.vertices + 5 * t.edges) := by
  rw [t.program_run, t.eval_correct]

/-- The arithmetic-instruction bound is linear in the represented tree size. -/
theorem Tree.program_operations_le (t : Tree K) :
    t.program.run.2 ≤ 5 * (t.vertices + t.edges) := by
  rw [t.program_run]
  simp only
  omega

omit [CommSemiring K]

mutual
/-- The represented connected structure has the tree edge/vertex count. -/
theorem Tree.edges_add_one_eq_vertices (t : Tree K) : t.edges + 1 = t.vertices := by
  cases t with
  | node a b ts => simp [Tree.edges, Tree.vertices, Forest.edges_eq_vertices, Nat.add_comm]
theorem Forest.edges_eq_vertices (ts : Forest K) : ts.edges = ts.vertices := by
  cases ts with
  | nil => rfl
  | cons p t ts =>
    have ht := t.edges_add_one_eq_vertices
    have hs := ts.edges_eq_vertices
    simp only [Forest.edges, Forest.vertices]
    omega
end

mutual
/-- The independent semantics enumerates exactly two choices per internal edge. -/
theorem Tree.card_choice (t : Tree K) : Fintype.card t.Choice = 2 ^ t.edges := by
  cases t with
  | node a b ts => exact ts.card_choice
theorem Forest.card_choice (ts : Forest K) : Fintype.card ts.Choice = 2 ^ ts.edges := by
  cases ts with
  | nil =>
    change Fintype.card Unit = 2 ^ 0
    simp
  | cons p t ts =>
    change Fintype.card (Bool × t.Choice × ts.Choice) = 2 ^ (1 + t.edges + ts.edges)
    simp [Fintype.card_prod, Tree.card_choice, Forest.card_choice, pow_add, mul_assoc]
end

end Holant.OneHot
