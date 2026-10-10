import Holant.OneHot.ArithmeticSize

/-!
# Intermediate-value bounds for the actual one-hot tree programs

The structural induction treats products of disjoint child/suffix subtrees by
adding their degree budgets. Addition contributes only one exponent bit. Every
executed operand/result has at most exponentially many monomials of linear degree.
-/

namespace Holant.OneHot

variable {K : Type*}

mutual
/-- Every literal coefficient stored in a tree satisfies `P`. -/
def Tree.All (P : K → Prop) : Tree K → Prop
  | .node a b ts => P a ∧ P b ∧ ts.All P
/-- Includes the parent's child-port coefficient at every forest cons. -/
def Forest.All (P : K → Prop) : Forest K → Prop
  | .nil => True
  | .cons p t ts => P p ∧ t.All P ∧ ts.All P
end

mutual
/-- Transport a predicate on all literal tree coefficients. -/
theorem Tree.All.mono {P Q : K → Prop} (t : Tree K) (h : t.All P)
    (hp : ∀ x, P x → Q x) : t.All Q := by
  cases t with
  | node a b ts => exact ⟨hp a h.1, hp b h.2.1, Forest.All.mono ts h.2.2 hp⟩
/-- Transport a predicate on all literal forest coefficients. -/
theorem Forest.All.mono {P Q : K → Prop} (ts : Forest K) (h : ts.All P)
    (hp : ∀ x, P x → Q x) : ts.All Q := by
  cases ts with
  | nil => trivial
  | cons p t ts => exact ⟨hp p h.1, Tree.All.mono t h.2.1 hp, Forest.All.mono ts h.2.2 hp⟩
end

namespace ArithmeticSize

variable {A : Type*} {coeff : A → K}

/-- The single budget controls both product degree and the binary logarithm of
the number of summands. It depends on graph size, not execution instruction count. -/
def treeBudget (t : Tree K) : ℕ := 2 * (t.vertices + t.edges)
def forestBudget (ts : Forest K) : ℕ := 2 * (ts.vertices + ts.edges)

@[simp] theorem treeBudget_node (a b : K) (ts : Forest K) :
    treeBudget (.node a b ts) = forestBudget ts + 2 := by
  simp only [treeBudget, forestBudget, Tree.vertices, Tree.edges]
  omega

@[simp] theorem forestBudget_nil : forestBudget (.nil : Forest K) = 0 := rfl

@[simp] theorem forestBudget_cons (p : K) (t : Tree K) (ts : Forest K) :
    forestBudget (.cons p t ts) = treeBudget t + forestBudget ts + 2 := by
  simp only [treeBudget, forestBudget, Forest.vertices, Forest.edges]
  omega

variable [CommSemiring K]

variable (aone : A) (hone : coeff aone = 1)

include hone

mutual
/-- The literal tree program's two results and every executed operand/result
have a structurally bounded sum-product expansion. -/
theorem tree_program_bound (t : Tree K) (h : t.All (Bound coeff 1)) :
    Bound coeff (treeBudget t) t.eval.1 ∧
    Bound coeff (treeBudget t) t.eval.2 ∧
    Arithmetic.Safe (Bound coeff (treeBudget t)) t.program := by
  cases t with
  | node a b ts =>
    rcases h with ⟨ha, hb, hs⟩
    rcases forest_program_bound ts hs with ⟨hs0, hs1, hsafe⟩
    have haz : Bound coeff (forestBudget ts + 1) (a * ts.eval.1) := by
      simpa [Nat.add_comm] using ha.mul hs0
    have hfree : Bound coeff (forestBudget ts + 2) (a * ts.eval.1 + ts.eval.2) := by
      simpa [Nat.add_assoc] using haz.add aone hone (hs1.mono aone hone (by omega))
    have hoccupied : Bound coeff (forestBudget ts + 2) (b * ts.eval.1) :=
      (hb.mul hs0).mono aone hone (by omega)
    rw [treeBudget_node]
    refine ⟨hfree, hoccupied, ?_⟩
    have has := ha.mono aone hone (show 1 ≤ forestBudget ts + 2 by omega)
    have hbs := hb.mono aone hone (show 1 ≤ forestBudget ts + 2 by omega)
    have hs0' := hs0.mono aone hone (show forestBudget ts ≤ forestBudget ts + 2 by omega)
    have hs1' := hs1.mono aone hone (show forestBudget ts ≤ forestBudget ts + 2 by omega)
    have haz' := haz.mono aone hone (show forestBudget ts + 1 ≤ forestBudget ts + 2 by omega)
    have hsafe' := hsafe.mono (fun _ hx => hx.mono aone hone
      (show forestBudget ts ≤ forestBudget ts + 2 by omega))
    simp only [Arithmetic.Safe, Tree.program, bind, pure, Arithmetic.values_bind,
      Forest.program_run, Arithmetic.run_mulOp, Arithmetic.run_addOp,
      Arithmetic.values_mulOp, Arithmetic.values_addOp,
      Arithmetic.values_pure, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_imp, forall_and, forall_eq] at *
    exact ⟨hsafe', ⟨has, hs0', haz'⟩, ⟨haz', hs1', hfree⟩, hbs, hs0', hoccupied⟩
/-- Forest products combine disjoint child and suffix subtrees. This is the
size argument that would fail for an unrestricted repeated-squaring program. -/
theorem forest_program_bound (ts : Forest K) (h : ts.All (Bound coeff 1)) :
    Bound coeff (forestBudget ts) ts.eval.1 ∧
    Bound coeff (forestBudget ts) ts.eval.2 ∧
    Arithmetic.Safe (Bound coeff (forestBudget ts)) ts.program := by
  cases ts with
  | nil => exact ⟨Bound.one, Bound.zero aone 0, Arithmetic.safe_pure _ _⟩
  | cons p t ts =>
    rcases h with ⟨hp, ht, hs⟩
    rcases tree_program_bound t ht with ⟨hc0, hc1, htc⟩
    rcases forest_program_bound ts hs with ⟨hs0, hs1, hsc⟩
    let B := treeBudget t + forestBudget ts + 2
    have hprod : Bound coeff B (t.eval.2 * ts.eval.1) :=
      (hc1.mul hs0).mono aone hone (by dsimp [B]; omega)
    have hpc : Bound coeff (1 + treeBudget t) (p * t.eval.1) := hp.mul hc0
    have hleft : Bound coeff (treeBudget t + forestBudget ts + 1)
        (p * t.eval.1 * ts.eval.1) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpc.mul hs0
    have hright : Bound coeff (treeBudget t + forestBudget ts + 1)
        (t.eval.2 * ts.eval.2) := (hc1.mul hs1).mono aone hone (by omega)
    have honeval : Bound coeff B
        (p * t.eval.1 * ts.eval.1 + t.eval.2 * ts.eval.2) := by
      simpa [B, Nat.add_assoc] using hleft.add aone hone hright
    rw [forestBudget_cons]
    refine ⟨hprod, honeval, ?_⟩
    have hp' : Bound coeff B p := hp.mono aone hone (by dsimp [B]; omega)
    have hc0' : Bound coeff B t.eval.1 := hc0.mono aone hone (by dsimp [B]; omega)
    have hc1' : Bound coeff B t.eval.2 := hc1.mono aone hone (by dsimp [B]; omega)
    have hs0' : Bound coeff B ts.eval.1 := hs0.mono aone hone (by dsimp [B]; omega)
    have hs1' : Bound coeff B ts.eval.2 := hs1.mono aone hone (by dsimp [B]; omega)
    have hpc' : Bound coeff B (p * t.eval.1) := hpc.mono aone hone (by dsimp [B]; omega)
    have hleft' := hleft.mono aone hone (show treeBudget t + forestBudget ts + 1 ≤ B by dsimp [B]; omega)
    have hright' := hright.mono aone hone (show treeBudget t + forestBudget ts + 1 ≤ B by dsimp [B]; omega)
    have htc' := htc.mono (fun _ hx => hx.mono aone hone
      (show treeBudget t ≤ B by dsimp [B]; omega))
    have hsc' := hsc.mono (fun _ hx => hx.mono aone hone
      (show forestBudget ts ≤ B by dsimp [B]; omega))
    change Arithmetic.Safe (Bound coeff B) _
    simp only [Arithmetic.Safe, Forest.program, bind, pure, Arithmetic.values_bind,
      Tree.program_run, Forest.program_run, Arithmetic.run_mulOp, Arithmetic.run_addOp,
      Arithmetic.values_mulOp, Arithmetic.values_addOp,
      Arithmetic.values_pure, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_imp, forall_and, forall_eq] at *
    exact ⟨htc', hsc', ⟨hc1', hs0', hprod⟩, ⟨hp', hc0', hpc'⟩, ⟨hpc', hs0', hleft'⟩,
      ⟨hc1', hs1', hright'⟩, hleft', hright', honeval⟩
end

/-- The genuine closed-root program inherits the same expansion control without
adding a supplied pin or a virtual-parent arithmetic operation. -/
theorem closed_program_bound (ts : Forest K) (a : K)
    (hs : ts.All (Bound coeff 1)) (ha : Bound coeff 1 a) :
    Bound coeff (forestBudget ts + 2) (ts.closedProgram a).run.1 ∧
    Arithmetic.Safe (Bound coeff (forestBudget ts + 2)) (ts.closedProgram a) := by
  rcases forest_program_bound aone hone ts hs with ⟨hs0, hs1, hsafe⟩
  have haz : Bound coeff (forestBudget ts + 1) (a * ts.eval.1) := by
    simpa [Nat.add_comm] using ha.mul hs0
  have hfree : Bound coeff (forestBudget ts + 2) (a * ts.eval.1 + ts.eval.2) := by
    simpa [Nat.add_assoc] using haz.add aone hone (hs1.mono aone hone (by omega))
  refine ⟨?_, ?_⟩
  · simpa only [Forest.closedProgram_run] using hfree
  · have has := ha.mono aone hone (show 1 ≤ forestBudget ts + 2 by omega)
    have hs0' := hs0.mono aone hone (show forestBudget ts ≤ forestBudget ts + 2 by omega)
    have hs1' := hs1.mono aone hone (show forestBudget ts ≤ forestBudget ts + 2 by omega)
    have haz' := haz.mono aone hone (show forestBudget ts + 1 ≤ forestBudget ts + 2 by omega)
    have hsafe' := hsafe.mono (fun _ hx => hx.mono aone hone
      (show forestBudget ts ≤ forestBudget ts + 2 by omega))
    simp only [Arithmetic.Safe, Forest.closedProgram, bind, Arithmetic.values_bind,
      Forest.program_run, Arithmetic.run_mulOp,
      Arithmetic.values_mulOp, Arithmetic.values_addOp,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq] at *
    exact ⟨hsafe', ⟨has, hs0', haz'⟩, haz', hs1', hfree⟩

end ArithmeticSize
end Holant.OneHot
