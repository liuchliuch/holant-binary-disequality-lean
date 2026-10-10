import Holant.Proofs.Counting.GateAlphabet
import Holant.Complexity.FixedGadgetSubstitution.WellFormed
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise


namespace Holant.LocalDrafts.CountingHardness.RawCompiler

open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open scoped BigOperators

def freshEdges {n : ℕ} : Circuit n → ℕ
  | .output _ => 0
  | .constant _ c => 1 + freshEdges c
  | .nand _ _ c => 5 + freshEdges c

def rows {n : ℕ} (c : Circuit n) (env : Fin n → RawEndpoint) (offset : ℕ) : List RawVertex :=
  match c with
  | .output out => List.ofFn fun i => (if i = out then 2 else 0, [env i])
  | .constant b c =>
    (if b then 2 else 1, [(offset, false)]) ::
      rows c (Fin.cons (offset, true) env) (offset + 1)
  | .nand a b c =>
    let env₁ := Function.update env a (offset, true)
    let env₂ := Function.update env₁ b (offset + 2, true)
    (3, [env a, (offset, false), (offset + 1, false)]) ::
    (3, [env₁ b, (offset + 2, false), (offset + 3, false)]) ::
    (4, [(offset + 1, true), (offset + 3, true), (offset + 4, false)]) ::
      rows c (Fin.cons (offset + 4, true) env₂) (offset + 5)

def compile (c : CircuitInstance) : RawClosedNetwork where
  vertices := (List.ofFn fun i : Fin c.inputs => (0, [(i.val, false)])) ++
    rows c.circuit (fun i => (i.val, true)) c.inputs
  edges := List.replicate (c.inputs + freshEdges c.circuit) 0

/-- Sum with arbitrary endpoint weights will prove multiplicity, not just support. -/
def portSum (f : RawEndpoint → ℕ) (vs : List RawVertex) : ℕ :=
  (((vs.map Prod.snd).flatten).map f).sum

def edgeSum (f : RawEndpoint → ℕ) (offset count : ℕ) : ℕ :=
  ((edgeEnds offset count).map f).sum

@[simp] theorem portSum_cons (f : RawEndpoint → ℕ) (v : RawVertex) (vs : List RawVertex) :
    portSum f (v :: vs) = (v.2.map f).sum + portSum f vs := by
  simp [portSum]

@[simp] theorem portSum_append (f : RawEndpoint → ℕ) (as bs : List RawVertex) :
    portSum f (as ++ bs) = portSum f as + portSum f bs := by simp [portSum]

theorem edgeSum_add (f : RawEndpoint → ℕ) (offset a b : ℕ) :
    edgeSum f offset (a + b) = edgeSum f offset a + edgeSum f (offset + a) b := by
  simp [edgeSum, edgeEnds_add]

theorem update_sum {n : ℕ} (env : Fin n → RawEndpoint) (a : Fin n)
    (p : RawEndpoint) (f : RawEndpoint → ℕ) :
    f (env a) + (∑ i, f (Function.update env a p i)) = f p + ∑ i, f (env i) := by
  classical
  have he : (fun i => f (Function.update env a p i)) =
      Function.update (fun i => f (env i)) a (f p) := by
    funext i
    by_cases hi : i = a <;> simp [hi]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ a)]
  have hs := Finset.add_sum_erase Finset.univ (fun i => f (env i)) (Finset.mem_univ a)
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

/-- Every old pending endpoint is consumed exactly once, and both ends of every
fresh edge are consumed exactly once. No injectivity assumption on `env` is used. -/
theorem rows_portSum {n : ℕ} (c : Circuit n) (env : Fin n → RawEndpoint)
    (offset : ℕ) (f : RawEndpoint → ℕ) :
    portSum f (rows c env offset) = (∑ i, f (env i)) + edgeSum f offset (freshEdges c) := by
  induction c generalizing offset with
  | output out => simp [rows, portSum, freshEdges, edgeSum, edgeEnds, List.map_ofFn, List.sum_ofFn]
  | constant b c ih =>
    have ht := ih (Fin.cons (offset, true) env) (offset + 1)
    rw [rows, portSum_cons, ht]
    simp only [freshEdges, edgeSum_add, Fin.sum_univ_succ]
    simp [edgeSum, edgeEnds, List.range_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | nand a b c ih =>
    let env₁ := Function.update env a (offset, true)
    let env₂ := Function.update env₁ b (offset + 2, true)
    have h₁ := update_sum env a (offset, true) f
    have h₂ := update_sum env₁ b (offset + 2, true) f
    have ht := ih (Fin.cons (offset + 4, true) env₂) (offset + 5)
    change portSum f ((3, [env a, (offset, false), (offset + 1, false)]) ::
      (3, [env₁ b, (offset + 2, false), (offset + 3, false)]) ::
      (4, [(offset + 1, true), (offset + 3, true), (offset + 4, false)]) ::
      rows c (Fin.cons (offset + 4, true) env₂) (offset + 5)) = _
    simp only [portSum_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, ht, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      freshEdges, edgeSum_add]
    have hblock : edgeSum f offset 5 =
        f (offset, false) + f (offset, true) +
        f (offset + 1, false) + f (offset + 1, true) +
        f (offset + 2, false) + f (offset + 2, true) +
        f (offset + 3, false) + f (offset + 3, true) +
        f (offset + 4, false) + f (offset + 4, true) := by
      simp [edgeSum, edgeEnds, List.range_succ, Nat.add_assoc]
    rw [hblock]
    change f (env a) + (∑ i, f (env₁ i)) = _ at h₁
    change f (env₁ b) + (∑ i, f (env₂ i)) = _ at h₂
    omega

theorem rows_labels {n : ℕ} (c : Circuit n) (env : Fin n → RawEndpoint) (offset : ℕ) :
    ∀ row ∈ rows c env offset,
      row.1 < 5 ∧ row.2.length = GateAlphabet.arity row.1 := by
  induction c generalizing offset with
  | output out =>
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    split_ifs <;> simp [GateAlphabet.arity]
  | constant b c ih =>
    intro row hr
    simp only [rows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · cases b <;> simp [GateAlphabet.arity]
    · exact ih _ _ row hr
  | nand a b c ih =>
    intro row hr
    simp only [rows, List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · simp [GateAlphabet.arity]
    · simp [GateAlphabet.arity]
    · simp [GateAlphabet.arity]
    · exact ih _ _ row hr

theorem initial_edgeSum (n : ℕ) (f : RawEndpoint → ℕ) :
    edgeSum f 0 n = (∑ i : Fin n, f (i.val, false)) + ∑ i : Fin n, f (i.val, true) := by
  let r : RawClosedNetwork := ⟨[], List.replicate n 0⟩
  have he := expectedEndpoints_eq r
  have hlength : r.edges.length = n := by simp [r]
  rw [hlength] at he
  rw [edgeSum, ← he]
  simp [RawClosedNetwork.expectedEndpoints, r, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, Finset.sum_add_distrib, Function.comp_def]

theorem compile_portSum (c : CircuitInstance) (f : RawEndpoint → ℕ) :
    portSum f (compile c).vertices = edgeSum f 0 (compile c).edges.length := by
  simp only [compile, List.length_replicate, portSum_append, rows_portSum]
  rw [edgeSum_add, initial_edgeSum]
  have hs : portSum f (List.ofFn fun i : Fin c.inputs => (0, [(i.val, false)])) =
      ∑ i : Fin c.inputs, f (i.val, false) := by
    simp [portSum, List.map_ofFn, List.sum_ofFn, List.map_flatten, List.sum_flatten,
      Function.comp_def]
  rw [hs]
  simp [Nat.add_assoc]

/-- The compiler targets the existing raw validator; no new graph semantics. -/
theorem compile_wellFormed (c : CircuitInstance) :
    (compile c).WellFormed 5 1 GateAlphabet.arity := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hm := List.get_mem (compile c).vertices v
    change (compile c).vertices.get v ∈
      (List.ofFn fun i : Fin c.inputs => (0, [(i.val, false)])) ++
        rows c.circuit (fun i => (i.val, true)) c.inputs at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
      rw [← hi]
      simp [GateAlphabet.arity]
    · exact rows_labels _ _ _ _ hm
  · intro e
    have hm := List.get_mem (compile c).edges e
    have he : (compile c).edges.get e = 0 := by
      exact List.eq_of_mem_replicate hm
    omega
  · apply List.perm_iff_count.mpr
    intro p
    have h := compile_portSum c (fun q => if q = p then 1 else 0)
    unfold edgeSum at h
    rw [← expectedEndpoints_eq (compile c)] at h
    have hc : ∀ xs : List RawEndpoint,
        (xs.map (fun q => if q = p then 1 else 0)).sum = xs.count p := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, List.count_cons, ih, beq_iff_eq]
        omega
    simpa only [portSum, RawClosedNetwork.endpoints, hc] using h

def validated (c : CircuitInstance) :
    {r : RawClosedNetwork // r.WellFormed 5 1 GateAlphabet.arity} :=
  ⟨compile c, compile_wellFormed c⟩

end Holant.LocalDrafts.CountingHardness.RawCompiler
