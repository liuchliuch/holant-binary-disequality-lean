import Holant.Tractable.Product
import Mathlib.Algebra.BigOperators.Ring.Finset


namespace Holant.LocalDrafts.Tractability.ProductElimination

open scoped BigOperators

variable {K : Type*} [CommSemiring K]

inductive Factor (K : Type*) (n : ℕ) where
  | scalar (c : K)
  | unary (port : Fin n) (values : Bool → K)
  | link (left right : Fin n) (flip : Bool)

def Factor.eval {n : ℕ} : Factor K n → (Fin n → Bool) → K
  | .scalar c, _ => c
  | .unary j u, x => u (x j)
  | .link a b p, x => if x a = Bool.xor (x b) p then 1 else 0

def weight {n : ℕ} (fs : List (Factor K n)) (x : Fin n → Bool) : K :=
  (fs.map (fun f => f.eval x)).prod

def partition {n : ℕ} (fs : List (Factor K n)) : K := ∑ x, weight fs x

@[simp] theorem weight_nil {n : ℕ} (x : Fin n → Bool) :
    weight ([] : List (Factor K n)) x = 1 := rfl

@[simp] theorem weight_cons {n : ℕ} (f : Factor K n) (fs : List (Factor K n))
    (x : Fin n → Bool) : weight (f :: fs) x = f.eval x * weight fs x := rfl

/-- Signed variable substitution preserves the restricted factor language. -/
def Factor.substitute {m n : ℕ} (r : Fin m → Fin n × Bool) : Factor K m → Factor K n
  | .scalar c => .scalar c
  | .unary j u => .unary (r j).1 (fun b => u (Bool.xor b (r j).2))
  | .link a b p => .link (r a).1 (r b).1 (Bool.xor (Bool.xor p (r a).2) (r b).2)

theorem Factor.substitute_eval {m n : ℕ} (r : Fin m → Fin n × Bool)
    (f : Factor K m) (x : Fin n → Bool) :
    (f.substitute r).eval x = f.eval (fun i => Bool.xor (x (r i).1) (r i).2) := by
  cases f with
  | scalar c => rfl
  | unary j u => rfl
  | link a b p =>
    have parity (u v s t p : Bool) :
        (if u = Bool.xor v (Bool.xor (Bool.xor p s) t) then (1 : K) else 0) =
          (if Bool.xor u s = Bool.xor (Bool.xor v t) p then 1 else 0) := by
      cases u <;> cases v <;> cases s <;> cases t <;> cases p <;> rfl
    exact parity (x (r a).1) (x (r b).1) (r a).2 (r b).2 p

theorem weight_substitute {m n : ℕ} (r : Fin m → Fin n × Bool)
    (fs : List (Factor K m)) (x : Fin n → Bool) :
    weight (fs.map (Factor.substitute r)) x =
      weight fs (fun i => Bool.xor (x (r i).1) (r i).2) := by
  simp only [weight, List.map_map, Function.comp_def, Factor.substitute_eval]

def redirect {n : ℕ} (j : Fin n) (p : Bool) : Fin (n + 1) → Fin n × Bool :=
  Fin.cases (j, p) (fun i => (i, false))

theorem redirect_word {n : ℕ} (j : Fin n) (p : Bool) (x : Fin n → Bool) :
    (fun i => Bool.xor (x (redirect j p i).1) (redirect j p i).2) =
      Fin.cons (Bool.xor (x j) p) x := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · simp [redirect]

/-- Only a link to a different variable is selected; self-links remain factors. -/
def Factor.pivot {n : ℕ} : Factor K (n + 1) → Option (Fin n × Bool)
  | .scalar _ => none
  | .unary _ _ => none
  | .link a b p =>
    Fin.cases (Fin.cases none (fun j => some (j, p)) b)
      (fun j => Fin.cases (some (j, p)) (fun _ => none) b) a

def pivot {n : ℕ} : List (Factor K (n + 1)) → Option (Fin n × Bool)
  | [] => none
  | f :: fs => match f.pivot with
    | some jp => some jp
    | none => pivot fs

theorem Factor.pivot_forces {n : ℕ} (f : Factor K (n + 1))
    (j : Fin n) (p : Bool) (h : f.pivot = some (j, p))
    (b : Bool) (x : Fin n → Bool) (hb : b ≠ Bool.xor (x j) p) :
    f.eval (Fin.cons b x) = 0 := by
  cases f with
  | scalar c => simp [Factor.pivot] at h
  | unary i u => simp [Factor.pivot] at h
  | link a c q =>
    revert h
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun c => ?_) c
      · simp [Factor.pivot]
      · intro h
        have hh : (c, q) = (j, p) := Option.some.inj h
        have hc : c = j := congrArg Prod.fst hh
        have hq : q = p := congrArg Prod.snd hh
        subst c
        subst q
        simpa [Factor.eval] using (if_neg hb : (if b = Bool.xor (x j) p then (1 : K) else 0) = 0)
    · refine Fin.cases ?_ (fun c => ?_) c
      · intro h
        have hh : (a, q) = (j, p) := Option.some.inj h
        have ha : a = j := congrArg Prod.fst hh
        have hq : q = p := congrArg Prod.snd hh
        subst a
        subst q
        cases b <;> cases hx : x j <;> cases p <;> simp_all [Factor.eval]
      · simp [Factor.pivot]

theorem pivot_forces {n : ℕ} (fs : List (Factor K (n + 1)))
    (j : Fin n) (p : Bool) (h : pivot fs = some (j, p))
    (b : Bool) (x : Fin n → Bool) (hb : b ≠ Bool.xor (x j) p) :
    weight fs (Fin.cons b x) = 0 := by
  induction fs with
  | nil => simp [pivot] at h
  | cons f fs ih =>
    cases hp : f.pivot with
    | none =>
      have ht : pivot fs = some (j, p) := by simpa [pivot, hp] using h
      simp [ih ht]
    | some jp =>
      have ht : jp = (j, p) := by simpa [pivot, hp] using h
      subst jp
      simp [f.pivot_forces j p hp b x hb]

/-- Split off head-only factors. The two impossible cross-link cases are zero;
the public split theorem rules them out using the computed absence of a pivot. -/
def Factor.splitHead {n : ℕ} : Factor K (n + 1) → (Bool → K) × Option (Factor K n)
  | .scalar c => (fun _ => 1, some (.scalar c))
  | .unary i u => Fin.cases (u, none) (fun j => (fun _ => 1, some (.unary j u))) i
  | .link a b p =>
    Fin.cases
      (Fin.cases ((fun t => if t = Bool.xor t p then 1 else 0), none)
        (fun _ => (fun _ => 0, none)) b)
      (fun a => Fin.cases (fun _ => 0, none)
        (fun b => (fun _ => 1, some (.link a b p))) b) a

def optionalEval {n : ℕ} (f : Option (Factor K n)) (x : Fin n → Bool) : K :=
  match f with
  | none => 1
  | some f => f.eval x

theorem Factor.splitHead_spec {n : ℕ} (f : Factor K (n + 1))
    (h : f.pivot = none) (b : Bool) (x : Fin n → Bool) :
    f.eval (Fin.cons b x) = (f.splitHead).1 b * optionalEval (f.splitHead).2 x := by
  cases f with
  | scalar c => simp [Factor.eval, Factor.splitHead, optionalEval]
  | unary i u =>
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [Factor.eval, Factor.splitHead, optionalEval]
  | link a c p =>
    revert h
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun c => ?_) c
      · intro _; simp [Factor.eval, Factor.splitHead, optionalEval]
      · simp [Factor.pivot]
    · refine Fin.cases ?_ (fun c => ?_) c
      · simp [Factor.pivot]
      · intro _; simp [Factor.eval, Factor.splitHead, optionalEval]

def headWeight {n : ℕ} (fs : List (Factor K (n + 1))) (b : Bool) : K :=
  (fs.map (fun f => f.splitHead.1 b)).prod

def tailFactors {n : ℕ} (fs : List (Factor K (n + 1))) : List (Factor K n) :=
  fs.filterMap (fun f => f.splitHead.2)

theorem no_pivot_cons {n : ℕ} (f : Factor K (n + 1)) (fs : List (Factor K (n + 1)))
    (h : pivot (f :: fs) = none) : f.pivot = none ∧ pivot fs = none := by
  cases hp : f.pivot with
  | none => exact ⟨rfl, by simpa [pivot, hp] using h⟩
  | some jp => simp [pivot, hp] at h

theorem weight_split {n : ℕ} (fs : List (Factor K (n + 1))) (h : pivot fs = none)
    (b : Bool) (x : Fin n → Bool) :
    weight fs (Fin.cons b x) = headWeight fs b * weight (tailFactors fs) x := by
  induction fs with
  | nil => simp [headWeight, tailFactors]
  | cons f fs ih =>
    obtain ⟨hf, ht⟩ := no_pivot_cons f fs h
    rw [weight_cons, f.splitHead_spec hf, ih ht]
    cases hs : f.splitHead.2 <;>
      simp [headWeight, tailFactors, List.filterMap_cons, hs, optionalEval] <;> ring

def headTail (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun x := (x 0, Fin.tail x)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := rfl

theorem partition_split {n : ℕ} (fs : List (Factor K (n + 1))) :
    partition fs = ∑ x : Fin n → Bool,
      (weight fs (Fin.cons false x) + weight fs (Fin.cons true x)) := by
  unfold partition
  rw [← (headTail n).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [headTail, Equiv.coe_fn_symm_mk, Finset.sum_add_distrib]
  ac_rfl

theorem partition_pivot {n : ℕ} (fs : List (Factor K (n + 1)))
    (j : Fin n) (p : Bool) (h : pivot fs = some (j, p)) :
    partition fs = partition (fs.map (Factor.substitute (redirect j p))) := by
  rw [partition_split, partition]
  apply Finset.sum_congr rfl
  intro x _
  rw [weight_substitute, redirect_word]
  cases hb : Bool.xor (x j) p with
  | false =>
    have hz := pivot_forces fs j p h true x (by simp [hb])
    simp [hb, hz]
  | true =>
    have hz := pivot_forces fs j p h false x (by simp [hb])
    simp [hb, hz]

theorem partition_isolated {n : ℕ} (fs : List (Factor K (n + 1)))
    (h : pivot fs = none) :
    partition fs = (headWeight fs false + headWeight fs true) * partition (tailFactors fs) := by
  rw [partition_split]
  simp_rw [weight_split fs h, ← add_mul]
  exact (Finset.mul_sum _ _ _).symm

/-- One recursive call, never two. The recursion is on the variable count. -/
def evaluate : {n : ℕ} → List (Factor K n) → K
  | 0, fs => weight fs Fin.elim0
  | n + 1, fs => match pivot fs with
    | some (j, p) => evaluate (fs.map (Factor.substitute (redirect j p)))
    | none => (headWeight fs false + headWeight fs true) * evaluate (tailFactors fs)

/-- Correctness follows from explicit finite-sum identities, not a supplied
algorithm specification or a presumed polynomial-time solver. -/
theorem evaluate_eq_partition {n : ℕ} (fs : List (Factor K n)) :
    evaluate fs = partition fs := by
  induction n with
  | zero =>
    calc
      evaluate fs = weight fs (default : Fin 0 → Bool) :=
        congrArg (weight fs) (Subsingleton.elim (Fin.elim0 : Fin 0 → Bool) default)
      _ = partition fs := by
        simp only [partition, Fintype.sum_unique]
        exact congrArg (weight fs) (Subsingleton.elim _ _)
  | succ n ih =>
    cases hp : pivot fs with
    | none =>
      simp only [evaluate, hp]
      rw [ih, partition_isolated fs hp]
    | some jp =>
      rcases jp with ⟨j, p⟩
      simp only [evaluate, hp]
      rw [ih, partition_pivot fs j p hp]

end Holant.LocalDrafts.Tractability.ProductElimination
