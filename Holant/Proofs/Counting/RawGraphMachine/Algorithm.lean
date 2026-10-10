import Holant.Proofs.Counting.CompilerSize
import Mathlib.Data.List.GetD


namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine
open Computability Holant.Complexity

abbrev Memory := List RawEndpoint × (ℕ × List RawVertex)
abbrev Work := Circuit.Code × Memory
abbrev Input := List Bool × Circuit.Code

def constant (b : Bool) (s : Memory) : Memory :=
  ((s.2.1, true) :: s.1, s.2.1 + 1,
    s.2.2 ++ [(if b then 2 else 1, [(s.2.1, false)])])

def nand (a b : ℕ) (s : Memory) : Memory :=
  let e₁ := s.1.set a (s.2.1, true)
  let e₂ := e₁.set b (s.2.1 + 2, true)
  ((s.2.1 + 4, true) :: e₂, s.2.1 + 5,
    s.2.2 ++ [(3, [s.1.getD a (0, false), (s.2.1, false), (s.2.1 + 1, false)]),
      (3, [e₁.getD b (0, false), (s.2.1 + 2, false), (s.2.1 + 3, false)]),
      (4, [(s.2.1 + 1, true), (s.2.1 + 3, true), (s.2.1 + 4, false)])])

def gate (s : Memory) (r : Circuit.Row) : Memory :=
  if r.1 < 2 then constant (decide (r.1 = 1)) s else nand r.2.1 r.2.2 s

def caps (out : ℕ) (env : List RawEndpoint) : List RawVertex :=
  (List.range env.length).map fun i =>
    (if i = out then 2 else 0, [env.getD i (0, false)])

def finish (out : ℕ) (s : Memory) : RawClosedNetwork :=
  ⟨s.2.2 ++ caps out s.1, List.replicate s.2.1 0⟩

def initial (x : Input) : Work :=
  (x.2, (List.range x.1.length).map (fun i => (i, true)), x.1.length,
    (List.range x.1.length).map (fun i => (0, [(i, false)])))

def advance (s : Work) : Work :=
  match s.1.1 with
  | [] => s
  | r :: rs => ((rs, s.1.2), gate s.2 r)

def result (s : Work) : RawClosedNetwork := finish s.1.2 s.2
def input (c : CircuitInstance) : Input := (List.replicate c.inputs false, c.circuit.code)

theorem getD_ofFn {A : Type} {n : ℕ} (f : Fin n → A) (i : Fin n) (d : A) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem set_ofFn {A : Type} {n : ℕ} (f : Fin n → A) (i : Fin n) (a : A) :
    (List.ofFn f).set i.val a = List.ofFn (Function.update f i a) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    by_cases h : j = i.val
    · subst j; simp
    · have hf : (⟨j, by simpa using hk⟩ : Fin n) ≠ i := fun e => h (congrArg Fin.val e)
      simp [List.getElem_set, h, Ne.symm h, Function.update, hf]

theorem range_map_eq_ofFn {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

theorem caps_ofFn {n : ℕ} (out : Fin n) (env : Fin n → RawEndpoint) :
    caps out.val (List.ofFn env) =
      List.ofFn (fun i : Fin n => (if i = out then 2 else 0, [env i])) := by
  apply List.ext_getElem
  · simp [caps]
  · intro i hi hj
    have hn : i < n := by simpa using hj
    have he : (⟨i, hn⟩ : Fin n) = out ↔ i = out.val := Fin.ext_iff
    simp [caps, getD_ofFn, he, List.getD_eq_getElem, hn]

theorem constant_ofFn {n : ℕ} (env : Fin n → RawEndpoint) (o : ℕ)
    (pre : List RawVertex) (b : Bool) :
    constant b (List.ofFn env, o, pre) =
      (List.ofFn (Fin.cons (o, true) env), o + 1,
        pre ++ [(if b then 2 else 1, [(o, false)])]) := by
  simp [constant, List.ofFn_succ]

theorem nand_ofFn {n : ℕ} (env : Fin n → RawEndpoint) (o : ℕ)
    (pre : List RawVertex) (a b : Fin n) :
    nand a.val b.val (List.ofFn env, o, pre) =
      (List.ofFn (Fin.cons (o + 4, true)
        (Function.update (Function.update env a (o, true)) b (o + 2, true))), o + 5,
        pre ++ [(3, [env a, (o, false), (o + 1, false)]),
          (3, [(Function.update env a (o, true)) b, (o + 2, false), (o + 3, false)]),
          (4, [(o + 1, true), (o + 3, true), (o + 4, false)])]) := by
  simp only [nand, set_ofFn, getD_ofFn]
  congr 2
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- Repeated inputs really read the newly allocated continuation of the first
copy vertex. There is no distinct-operands premise. -/
theorem repeated_operand {n : ℕ} (env : Fin n → RawEndpoint) (o : ℕ) (a : Fin n) :
    ((List.ofFn env).set a.val (o, true)).getD a.val (0, false) = (o, true) := by
  rw [set_ofFn, getD_ofFn]
  simp

/-- Strong accumulator equality includes old prefix, all final caps, and the
exact final edge count. No graph-permutation quotient is used. -/
theorem fold_exact {n : ℕ} (c : Circuit n) (env : Fin n → RawEndpoint)
    (o : ℕ) (pre : List RawVertex) :
    finish c.code.2 (c.code.1.foldl gate (List.ofFn env, o, pre)) =
      ⟨pre ++ RawCompiler.rows c env o, List.replicate (o + RawCompiler.freshEdges c) 0⟩ := by
  induction c generalizing o pre with
  | output out => simp [Circuit.code, finish, caps_ofFn, RawCompiler.rows, RawCompiler.freshEdges]
  | constant b c ih =>
    have hg : gate (List.ofFn env, o, pre) (if b then 1 else 0, 0, 0) =
        constant b (List.ofFn env, o, pre) := by cases b <;> rfl
    simp only [Circuit.code, List.foldl_cons]
    rw [hg, constant_ofFn, ih]
    simp [RawCompiler.rows, RawCompiler.freshEdges, List.append_assoc, Nat.add_assoc]
  | nand a b c ih =>
    simp only [Circuit.code, List.foldl_cons, gate, lt_self_iff_false, if_false]
    rw [nand_ofFn, ih]
    simp [RawCompiler.rows, RawCompiler.freshEdges, List.append_assoc, Nat.add_assoc]

theorem advance_many (rows : List Circuit.Row) (out : ℕ) (s : Memory) (k : ℕ)
    (hk : rows.length ≤ k) :
    (advance^[k]) ((rows, out), s) = (([], out), rows.foldl gate s) := by
  induction k generalizing rows s with
  | zero => have h : rows = [] := List.length_eq_zero_iff.mp (by omega); subst rows; rfl
  | succ k ih =>
    cases rows with
    | nil => simpa [Function.iterate_succ_apply, advance] using ih [] s (by simp)
    | cons r rs =>
      simpa only [Function.iterate_succ_apply, advance, List.foldl_cons] using
        ih rs (gate s r) (by simpa using Nat.le_of_succ_le_succ hk)

theorem result_exact (c : CircuitInstance) (k : ℕ) (hk : c.circuit.gates ≤ k) :
    result ((advance^[k]) (initial (input c))) = RawCompiler.compile c := by
  simp only [initial, input, List.length_replicate]
  rw [range_map_eq_ofFn, range_map_eq_ofFn,
    advance_many _ _ _ k (by simpa using hk)]
  exact fold_exact c.circuit (fun i => (i.val, true)) c.inputs
    (List.ofFn fun i : Fin c.inputs => (0, [(i.val, false)]))

end Holant.LocalDrafts.CountingHardness.RawGraphMachine
