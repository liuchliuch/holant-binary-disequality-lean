import Holant.Proofs.Tractability.ProductMachine.Expression
import Holant.Proofs.Tractability.ProductFixedField


namespace Holant.LocalDrafts.Tractability.ProductMachine.Symbolic

open Holant.LocalDrafts.Tractability
variable {A K : Type} [CommSemiring K]

def atom {n : ℕ} : ProductElimination.LabelledFactor A n → (Fin n → Bool) → Expr A
  | .scalar a, _ => .literal a
  | .unary j a, x => .literal (a (x j))
  | .link i j p, x => if x i = Bool.xor (x j) p then .one else .zero

theorem atom_eval {n : ℕ} (coeff : A → K) (f : ProductElimination.LabelledFactor A n) (x : Fin n → Bool) :
    (atom f x).eval coeff = (f.realize coeff).eval x := by
  cases f with
  | scalar a => rfl
  | unary j a => rfl
  | link i j p =>
    by_cases h : x i = Bool.xor (x j) p <;>
      simp [atom,h,Expr.eval,ProductElimination.LabelledFactor.realize,
        ProductElimination.Factor.eval]

theorem atom_size {n : ℕ} (f : ProductElimination.LabelledFactor A n) (x : Fin n → Bool) : (atom f x).size = 1 := by
  cases f <;> simp [atom, apply_ite, Expr.size]

def substitute {m n : ℕ} (r : Fin m → Fin n × Bool) : ProductElimination.LabelledFactor A m → ProductElimination.LabelledFactor A n
  | .scalar a => .scalar a
  | .unary j a => .unary (r j).1 (fun b => a (Bool.xor b (r j).2))
  | .link i j p => .link (r i).1 (r j).1 (Bool.xor (Bool.xor p (r i).2) (r j).2)

theorem substitute_realize {m n : ℕ} (coeff : A → K) (r : Fin m → Fin n × Bool)
    (f : ProductElimination.LabelledFactor A m) :
    (substitute r f).realize coeff = (f.realize coeff).substitute r := by cases f <;> rfl

/-- Zero interpretation only erases labels; pivot inspects incidence and parity. -/
def pivot {n : ℕ} (fs : List (ProductElimination.LabelledFactor A (n + 1))) : Option (Fin n × Bool) :=
  ProductElimination.pivot (fs.map (ProductElimination.LabelledFactor.realize (fun _ => (0 : ℕ))))

theorem pivot_realize {n : ℕ} (coeff : A → K) (fs : List (ProductElimination.LabelledFactor A (n + 1))) :
    ProductElimination.pivot (fs.map (ProductElimination.LabelledFactor.realize coeff)) = pivot fs := by
  have one (f : ProductElimination.LabelledFactor A (n + 1)) :
      (f.realize coeff).pivot = (f.realize (fun _ => (0 : ℕ))).pivot := by cases f <;> rfl
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, ProductElimination.pivot, one]
    change ProductElimination.pivot (fs.map (ProductElimination.LabelledFactor.realize coeff)) =
      ProductElimination.pivot (fs.map (ProductElimination.LabelledFactor.realize (fun _ => (0 : ℕ)))) at ih
    rw [ih]
    rfl

def splitHead {n : ℕ} : ProductElimination.LabelledFactor A (n + 1) → (Bool → Expr A) × Option (ProductElimination.LabelledFactor A n)
  | .scalar a => (fun _ => .one, some (.scalar a))
  | .unary j a => Fin.cases ((fun b => .literal (a b)), none)
      (fun j => (fun _ => .one, some (.unary j a))) j
  | .link i j p =>
    Fin.cases
      (Fin.cases ((fun b => if b = Bool.xor b p then .one else .zero), none)
        (fun _ => (fun _ => .zero, none)) j)
      (fun i => Fin.cases (fun _ => .zero, none)
        (fun j => (fun _ => .one, some (.link i j p))) j) i

theorem splitHead_realize {n : ℕ} (coeff : A → K) (f : ProductElimination.LabelledFactor A (n + 1)) :
    (f.realize coeff).splitHead =
      ((fun b => ((splitHead f).1 b).eval coeff), (splitHead f).2.map (ProductElimination.LabelledFactor.realize coeff)) := by
  cases f with
  | scalar a => rfl
  | unary j a => refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  | link i j p =>
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · apply Prod.ext
        · funext b
          cases b <;> cases p <;> rfl
        · rfl
      · rfl
    · refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem splitHead_size {n : ℕ} (f : ProductElimination.LabelledFactor A (n + 1)) (b : Bool) :
    ((splitHead f).1 b).size = 1 := by
  cases f with
  | scalar a => rfl
  | unary j a => refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  | link i j p =>
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [splitHead, apply_ite, Expr.size]
      · rfl
    · refine Fin.cases ?_ (fun j => ?_) j <;> rfl

def head {n : ℕ} (fs : List (ProductElimination.LabelledFactor A (n + 1))) (b : Bool) : Expr A :=
  Expr.product (fs.map (fun f => (splitHead f).1 b))

def tail {n : ℕ} (fs : List (ProductElimination.LabelledFactor A (n + 1))) : List (ProductElimination.LabelledFactor A n) :=
  fs.filterMap (fun f => (splitHead f).2)

theorem head_eval {n : ℕ} (coeff : A → K) (fs : List (ProductElimination.LabelledFactor A (n + 1))) (b : Bool) :
    (head fs b).eval coeff =
      ProductElimination.headWeight (fs.map (ProductElimination.LabelledFactor.realize coeff)) b := by
  simp [head, Expr.eval_product, ProductElimination.headWeight, List.map_map,
    Function.comp_def, splitHead_realize]

theorem tail_realize {n : ℕ} (coeff : A → K) (fs : List (ProductElimination.LabelledFactor A (n + 1))) :
    (tail fs).map (ProductElimination.LabelledFactor.realize coeff) =
      ProductElimination.tailFactors (fs.map (ProductElimination.LabelledFactor.realize coeff)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [tail, ProductElimination.tailFactors, List.map_cons, List.filterMap_cons,
      splitHead_realize] at *
    cases (splitHead f).2 <;> simp_all

theorem tail_length {n : ℕ} (fs : List (ProductElimination.LabelledFactor A (n + 1))) : (tail fs).length ≤ fs.length := by
  exact List.length_filterMap_le _ _

theorem head_size {n : ℕ} (fs : List (ProductElimination.LabelledFactor A (n + 1))) (b : Bool) :
    (head fs b).size ≤ 2 * fs.length + 1 := by
  apply (Expr.size_product_le _ ?_).trans (by simp)
  intro e he
  obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
  exact le_of_eq (splitHead_size f b)

def compile : {n : ℕ} → List (ProductElimination.LabelledFactor A n) → Expr A
  | 0, fs => Expr.product (fs.map (fun f => atom f Fin.elim0))
  | n + 1, fs => match pivot fs with
    | some (j, p) => compile (fs.map (substitute (ProductElimination.redirect j p)))
    | none => .mul (.add (head fs false) (head fs true)) (compile (tail fs))

/-- Semantic correctness is derived from the earlier explicit elimination proof,
not accepted as an input to a purported encoded compiler. -/
theorem compile_eval {n : ℕ} (coeff : A → K) (fs : List (ProductElimination.LabelledFactor A n)) :
    (compile fs).eval coeff = ProductElimination.evaluate (fs.map (ProductElimination.LabelledFactor.realize coeff)) := by
  induction n with
  | zero => simp [compile, Expr.eval_product, List.map_map, Function.comp_def, atom_eval,
      ProductElimination.evaluate, ProductElimination.weight]
  | succ n ih =>
    cases hp : pivot fs with
    | none => simp [compile, hp, Expr.eval, ih, ProductElimination.evaluate,
        pivot_realize, head_eval, tail_realize]
    | some jp =>
      rcases jp with ⟨j, p⟩
      simp [compile, hp, ih, ProductElimination.evaluate, pivot_realize,
        List.map_map, Function.comp_def, substitute_realize]

def budget (n m : ℕ) := (4 * n + 2) * m + 4 * n + 1

theorem compile_size {n : ℕ} (fs : List (ProductElimination.LabelledFactor A n)) :
    (compile fs).size ≤ budget n fs.length := by
  induction n with
  | zero =>
    have h := Expr.size_product_le (fs.map (fun f => atom f Fin.elim0)) (by
      intro e he
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
      exact le_of_eq (atom_size f Fin.elim0))
    simpa [compile, budget] using h
  | succ n ih =>
    cases hp : pivot fs with
    | none =>
      have hf := head_size fs false
      have ht := head_size fs true
      have hr := ih (tail fs)
      have hl := Nat.mul_le_mul_left (4 * n + 2) (tail_length fs)
      simp only [compile, hp, Expr.size]
      unfold budget at *
      nlinarith
    | some jp =>
      rcases jp with ⟨j, p⟩
      have h := ih (fs.map (substitute (ProductElimination.redirect j p)))
      simp only [List.length_map] at h
      simp only [compile, hp]
      unfold budget at *
      nlinarith

end Holant.LocalDrafts.Tractability.ProductMachine.Symbolic
