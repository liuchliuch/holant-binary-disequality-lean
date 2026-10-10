import Holant.OneHot.ArithmeticSizeTree
import Holant.OneHot.Decomposition.AllComponents

/-!
# Structural intermediate-value bounds for original graph programs

Coefficient bounds are transported through actual graph extraction and edge
conditioning. The finite component product adds the budgets of disjoint original
vertex sets. Bounds hold for every executed operand and result, not only the
final network answer. Graph extraction itself remains semantic here.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot

variable {K : Type*}

/-- Assembling children introduces only their literal supplied coefficients. -/
theorem Forest.all_ofFn {P : K → Prop} {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K)
    (hb : ∀ i, P (b i)) (ht : ∀ i, (ts i).All P) : (Forest.ofFn b ts).All P := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hb 0, ht 0, ih _ _ (fun i => hb i.succ) (fun i => ht i.succ)⟩

namespace Decomposition.RootedSpanning

variable {V E : Type*} {endpoint : E → Bool → V} {root : V}
variable (t : RootedSpanning endpoint root) [Fintype V]

open scoped Classical

/-- Literal unfolding preserves every input coefficient predicate. -/
theorem unfold_all {P : K → Prop} (a b : V → K) (port : {v : V // v ≠ root} → K)
    (ha : ∀ v, P (a v)) (hb : ∀ v, P (b v)) (hp : ∀ u, P (port u)) (v : V) :
    (t.unfold a b port v).tree.All P := by
  induction v using (measure (fun v => Fintype.card (t.Descendant v))).wf.induction with
  | h v ih =>
    rw [unfold]
    refine ⟨ha v, hb v, Forest.all_ofFn _ _ (fun _ => hp _) ?_⟩
    intro i
    exact ih _ (t.descendant_card_child_lt _ _)

end Decomposition.RootedSpanning

namespace ArithmeticSize

variable {A : Type*} [CommSemiring K] {coeff : A → K}
variable (aone : A) (hone : coeff aone = 1)
include hone

/-- The closed `Tree` wrapper executes precisely the already bounded forest
program, and does not evaluate its unused virtual-parent coefficient. -/
theorem tree_closed_program_bound (t : Tree K) (h : t.All (Bound coeff 1)) :
    Bound coeff (treeBudget t) t.closedProgram.run.1 ∧
    Arithmetic.Safe (Bound coeff (treeBudget t)) t.closedProgram := by
  cases t with
  | node a b ts =>
    simpa only [treeBudget_node, Tree.closedProgram] using
      closed_program_bound aone hone ts a h.2.2 h.1

/-- A finite product's budget is the sum of its component budgets, rather than
a multiple of the total instruction count. All actual partial products are covered. -/
theorem finiteProduct_bound {n : ℕ} (p : Fin n → Arithmetic K K) (b : Fin n → ℕ)
    (h : ∀ i, Bound coeff (b i) (p i).run.1 ∧ Arithmetic.Safe (Bound coeff (b i)) (p i)) :
    Bound coeff (∑ i, b i) (Arithmetic.finiteProduct p).run.1 ∧
    Arithmetic.Safe (Bound coeff (∑ i, b i)) (Arithmetic.finiteProduct p) := by
  induction n with
  | zero => exact ⟨Bound.one, Arithmetic.safe_pure _ _⟩
  | succ n ih =>
    rcases h 0 with ⟨hx, hpx⟩
    rcases ih (fun i => p i.succ) (fun i => b i.succ) (fun i => h i.succ) with ⟨hy, hpy⟩
    rw [Fin.sum_univ_succ]
    let y := (Arithmetic.finiteProduct (fun i : Fin n => p i.succ)).run.1
    have hz := hx.mul hy
    refine ⟨?_, ?_⟩
    · simpa only [Arithmetic.finiteProduct, bind, Arithmetic.run_bind,
        Arithmetic.run_mulOp] using hz
    · apply Arithmetic.safe_bind
        (hpx.mono (fun _ hx => hx.mono aone hone (Nat.le_add_right _ _)))
      apply Arithmetic.safe_bind
        (hpy.mono (fun _ hy => hy.mono aone hone (Nat.le_add_left _ _)))
      exact Arithmetic.safe_mulOp
        (hx.mono aone hone (Nat.le_add_right _ _))
        (hy.mono aone hone (Nat.le_add_left _ _)) hz

end ArithmeticSize
end Holant.OneHot

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.ArithmeticSize

variable {K A : Type*} [CommSemiring K] {coeff : A → K}
variable (N : Network K 0) (aone : A) (hone : coeff aone = 1)
include aone hone

open scoped Classical

omit hone in
/-- Original table entries are the only nonzero inputs to the actual unfolding. -/
theorem extractedTree_all {root : Fin N.shape.vertices}
    (t : RootedSpanning N.shape.endpoint root)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    (N.extractedTree t).All (Bound coeff 1) := by
  apply t.unfold_all
  · intro v
    exact h v _
  · intro v
    dsimp [treeParent]
    split
    · exact Bound.zero aone 1
    · exact h _ _
  · intro u
    exact h _ _

/-- The extracted spanning-tree arithmetic has a linear budget in the number of
original vertices, even before assuming the graph itself is a tree. -/
theorem connectedTree_program_bound (root : Fin N.shape.vertices)
    (connected : ∀ v, N.shape.Reachable root v)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * N.shape.vertices) (N.connectedTree root connected).closedProgram.run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * N.shape.vertices))
      (N.connectedTree root connected).closedProgram := by
  let t := extractRootedSpanning N.shape.endpoint root connected
  have hb := tree_closed_program_bound aone hone (N.extractedTree t)
    (N.extractedTree_all aone t h)
  have hv : (N.extractedTree t).vertices = N.shape.vertices := by
    simpa only [extractedTree, Fintype.card_fin] using
      t.unfold_vertices N.treeZero (N.treeParent t) (N.treeChild t)
  have he := (N.extractedTree t).edges_add_one_eq_vertices
  have hbudget : treeBudget (N.extractedTree t) ≤ 4 * N.shape.vertices := by
    dsimp [treeBudget]
    omega
  exact ⟨hb.1.mono aone hone hbudget, hb.2.mono (fun _ hx => hx.mono aone hone hbudget)⟩

end Holant.Network

namespace Holant.FiniteNetwork

open OneHot OneHot.Decomposition OneHot.ArithmeticSize

variable {K A V E : Type*} [CommSemiring K] [Fintype V] [Fintype E]
variable {coeff : A → K} (N : FiniteNetwork K V E 0) (aone : A) (hone : coeff aone = 1)
include hone

open scoped Classical

theorem connectedTreeProgram_bound (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * Fintype.card V) (N.connectedTreeProgram root connected).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * Fintype.card V)) (N.connectedTreeProgram root connected) :=
  N.toNetwork.connectedTree_program_bound aone hone (Fintype.equivFin V root)
    (N.toNetwork_connected root connected) (fun v => h ((Fintype.equivFin V).symm v))

/-- Edge conditioning evaluates an original table on a filled assignment, so it
does not enlarge the coefficient family, including for self-loops. -/
theorem conditionedTreeProgram_bound {root : V} (t : RootedSpanning N.endpoint root)
    (e : t.Surplus) (a b : Bool) (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * Fintype.card V) (N.conditionedTreeProgram t e a b).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * Fintype.card V)) (N.conditionedTreeProgram t e a b) := by
  apply (N.conditionEdge e.1 a b).connectedTreeProgram_bound aone hone
    root (N.conditionEdge_connected t e a b)
  intro v x
  exact h v _

/-- Two actual residual-tree executions followed by one addition. -/
theorem spanningUnicycleProgram_bound {root : V} (t : RootedSpanning N.endpoint root)
    (e : t.Surplus) (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * Fintype.card V + 1) (N.spanningUnicycleProgram t e).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * Fintype.card V + 1)) (N.spanningUnicycleProgram t e) := by
  rcases N.conditionedTreeProgram_bound aone hone t e false true h with ⟨hx, hpx⟩
  rcases N.conditionedTreeProgram_bound aone hone t e true false h with ⟨hy, hpy⟩
  have hz := hx.add aone hone hy
  refine ⟨?_, ?_⟩
  · simpa only [spanningUnicycleProgram, bind, Arithmetic.run_bind, Arithmetic.run_addOp] using hz
  · apply Arithmetic.safe_bind (hpx.mono (fun _ hx => hx.mono aone hone (by omega)))
    apply Arithmetic.safe_bind (hpy.mono (fun _ hy => hy.mono aone hone (by omega)))
    exact Arithmetic.safe_addOp (hx.mono aone hone (by omega))
      (hy.mono aone hone (by omega)) hz

theorem connectedProgram_bound (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (4 * Fintype.card V + 1) (N.connectedProgram root connected).run.1 ∧
    Arithmetic.Safe (Bound coeff (4 * Fintype.card V + 1)) (N.connectedProgram root connected) := by
  unfold connectedProgram
  split
  · exact ⟨Bound.zero aone _, Arithmetic.safe_pure _ _⟩
  · split
    · have hb := N.connectedTreeProgram_bound aone hone root connected h
      exact ⟨hb.1.mono aone hone (by omega), hb.2.mono (fun _ hx => hx.mono aone hone (by omega))⟩
    · exact N.spanningUnicycleProgram_bound aone hone _ _ h

end Holant.FiniteNetwork

namespace Holant.Network

open OneHot OneHot.Decomposition OneHot.ArithmeticSize

variable {K A : Type*} [CommSemiring K] {coeff : A → K}
variable (N : Network K 0) (aone : A) (hone : coeff aone = 1)
include hone

open scoped Classical

/-- Every executed operand/result of the original-network arithmetic program,
and its final return value, is a sum of at most `2^(5V)` fixed-coefficient
monomials of degree `5V`. Disjoint component sizes add to the original size.
This theorem bounds actual arithmetic values; it is not a bit-time theorem. -/
theorem oneHotProgram_bound (h : ∀ v x, Bound coeff 1 (N.vertex v x)) :
    Bound coeff (5 * N.shape.vertices) N.oneHotProgram.run.1 ∧
    Arithmetic.Safe (Bound coeff (5 * N.shape.vertices)) N.oneHotProgram := by
  let en := (Fintype.equivFin N.shape.Component).symm
  let b (i : Fin (Fintype.card N.shape.Component)) :=
    4 * Fintype.card (N.shape.ComponentVertex (en i)) + 1
  have hb := finiteProduct_bound aone hone
    (fun i => N.componentProgram (en i)) b (fun i =>
      (N.componentFiniteNetwork (en i)).connectedProgram_bound aone hone
        (N.shape.componentRoot (en i)) (N.componentFiniteNetwork_connected (en i))
        (fun v => h v.1))
  have hbudget : (∑ i, b i) ≤ 5 * N.shape.vertices := by
    have hc : Fintype.card N.shape.Component ≤ N.shape.vertices := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
        N.shape.componentOf N.shape.componentOf_surjective
    have hs : (∑ i, b i) = 4 * N.shape.vertices + Fintype.card N.shape.Component := by
      simp only [b, Finset.sum_add_distrib, ← Finset.mul_sum,
        en.sum_comp (fun c => Fintype.card (N.shape.ComponentVertex c)),
        N.shape.sum_componentVertex_card, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  exact ⟨hb.1.mono aone hone hbudget, hb.2.mono (fun _ hx => hx.mono aone hone hbudget)⟩

end Holant.Network
