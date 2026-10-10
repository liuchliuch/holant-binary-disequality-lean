import Holant.OneHot.Computable.SemanticSpanning

/-!
# Executable component and parent tables

These are ordinary finite output lists, suitable for later serialization and
machine compilation. The component counter is accumulated by the executed
reachability calls themselves. It counts endpoint tests only, as in Reachability.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Computable.Graph

open Holant.OneHot.Decomposition

variable (g : Graph)

/-- A serializable row for one original vertex. Parent edge numbers are the
original edge IDs; the Boolean marks the child's original end occurrence. -/
structure ParentRow where
  component : ℕ
  depth : ℕ
  parent : Option (ℕ × Bool)
  deriving DecidableEq, Repr

def labelledVertex (v : g.Vertex) : g.Fiber (g.label v) :=
  ⟨v, (g.reach_iff _ _).mpr (.symm _ _ (g.label_reachable v))⟩

def parentRow (v : g.Vertex) : ParentRow :=
  let root := g.label v
  let u := g.labelledVertex v
  ⟨root.val, g.depth root u,
    if h : u = g.fiberRoot root then none
    else let q := g.parentEnd root ⟨u, h⟩; some (q.1.val, q.2)⟩

/-- The table has a row even for every isolated or nullary vertex. -/
def parentTable : List ParentRow := (List.finRange g.vertices).map g.parentRow

@[simp] theorem parentTable_length : g.parentTable.length = g.vertices := by simp [parentTable]

@[simp] theorem parentRow_component (v : g.Vertex) :
    (g.parentRow v).component = (g.label v).val := rfl

theorem parentRow_depth_le (v : g.Vertex) : (g.parentRow v).depth ≤ g.vertices :=
  g.depth_le _ _

/-- Exactly the chosen least-vertex roots have no parent in the output table. -/
theorem parentRow_none_iff (v : g.Vertex) :
    (g.parentRow v).parent = none ↔ g.label v = v := by
  simp only [parentRow]
  split
  · rename_i h
    have hh : v = g.label v := congrArg Subtype.val h
    exact ⟨fun _ => hh.symm, fun _ => rfl⟩
  · rename_i h
    have hn : g.label v ≠ v := by
      intro hh
      apply h
      apply Subtype.ext
      exact hh.symm
    simp [hn]

/-- Every non-root row stores a valid original edge end at that very vertex,
and following its opposite endpoint strictly decreases the stored table rank. -/
theorem parentRow_some_spec (v : g.Vertex) (q : ℕ × Bool)
    (hp : (g.parentRow v).parent = some q) :
    ∃ e : g.Edge, e.val = q.1 ∧ g.endpoint e q.2 = v ∧
      (g.parentRow (g.endpoint e (!q.2))).depth < (g.parentRow v).depth := by
  dsimp only [parentRow] at hp
  split at hp
  · contradiction
  · rename_i hn
    let u : {u : g.Fiber (g.label v) // u ≠ g.fiberRoot (g.label v)} :=
      ⟨g.labelledVertex v, hn⟩
    let chosen := g.parentEnd (g.label v) u
    have hq : (chosen.1.val, chosen.2) = q := Option.some.inj hp
    subst q
    have hc : g.endpoint chosen.1 chosen.2 = v := (g.parentEnd_spec _ u).1
    have ha : Relation.EqvGen (Link g.endpoint) (g.endpoint chosen.1 (!chosen.2)) v := by
      rw [← hc]
      cases hb : chosen.2
      · exact .symm _ _ (.rel _ _ ⟨chosen.1, rfl, rfl⟩)
      · exact .rel _ _ ⟨chosen.1, rfl, rfl⟩
    have hl := g.label_eq_of_reachable ha
    refine ⟨chosen.1, rfl, hc, ?_⟩
    have ht := (g.rootedSpanning (g.label v)).parent_depth_lt u
    change g.depth (g.label v) _ < g.depth (g.label v) (g.labelledVertex v) at ht
    change g.depth (g.label (g.endpoint chosen.1 (!chosen.2))) _ <
      g.depth (g.label v) (g.labelledVertex v)
    have dc {r₁ r₂ : g.Vertex} (hr : r₁ = r₂) (a : g.Fiber r₁) (b : g.Fiber r₂)
        (hab : a.1 = b.1) : g.depth r₁ a = g.depth r₂ b := by
      subst r₂
      have he : a = b := Subtype.ext hab
      rw [he]
    have hd := dc hl (g.labelledVertex (g.endpoint chosen.1 (!chosen.2)))
      (g.fiberEndpoint (g.label v) ((g.rootedSpanning (g.label v)).parentEnd u).1
        (!((g.rootedSpanning (g.label v)).parentEnd u).2)) rfl
    exact hd.trans_lt ht

/-- A computed component label, sharing the actual instrumented search result. -/
def labelRun (v : g.Vertex) : g.Vertex × ℕ :=
  let run := g.reachRun v g.vertices
  (run.1.min' ⟨v, g.root_mem_reach v _⟩, run.2)

@[simp] theorem labelRun_value (v : g.Vertex) : (g.labelRun v).1 = g.label v := rfl

def labelsRun : List g.Vertex × ℕ :=
  let rows := (List.finRange g.vertices).map g.labelRun
  (rows.map Prod.fst, (rows.map Prod.snd).sum)

@[simp] theorem labelsRun_value : (g.labelsRun).1 = (List.finRange g.vertices).map g.label := by
  simp [labelsRun, List.map_map, Function.comp_def]

/-- Polynomial bound for the actual accumulated component-search counter. This
is not a claim about bit-level equality, parsing, allocation or TM2 transitions. -/
theorem labelsRun_tests_le :
    g.labelsRun.2 ≤ g.vertices * (g.vertices * (2 * g.vertices * g.edges.length)) := by
  have bound (xs : List g.Vertex) :
      (xs.map fun v => (g.labelRun v).2).sum ≤ xs.length *
        (g.vertices * (2 * g.vertices * g.edges.length)) := by
    induction xs with
    | nil => simp
    | cons v xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hv := g.reach_work_le v g.vertices
      change (g.labelRun v).2 ≤ g.vertices * (2 * g.vertices * g.edges.length) at hv
      omega
  simpa [labelsRun, List.map_map, Function.comp_def] using bound (List.finRange g.vertices)

end Holant.OneHot.Computable.Graph

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot.Computable

variable {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)

theorem graph_component_tests_le_bits (h : r.WellFormed s b arity) :
    (r.graph h).labelsRun.2 ≤ 2 * (encoding.encode r).length ^ 4 := by
  have hc := (r.graph h).labelsRun_tests_le
  rw [r.graph_edges h] at hc
  change (r.graph h).labelsRun.2 ≤ r.vertices.length *
    (r.vertices.length * (2 * r.vertices.length * r.edges.length)) at hc
  have hn := r.counts_le_encoded_length
  have hv : r.vertices.length ≤ (encoding.encode r).length := by omega
  have he : r.edges.length ≤ (encoding.encode r).length := by omega
  calc
    _ ≤ r.vertices.length * (r.vertices.length * (2 * r.vertices.length * r.edges.length)) := hc
    _ ≤ (encoding.encode r).length * ((encoding.encode r).length *
      (2 * (encoding.encode r).length * (encoding.encode r).length)) :=
      Nat.mul_le_mul hv (Nat.mul_le_mul hv (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hv) he))
    _ = _ := by simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]

end Holant.Complexity.RawClosedNetwork

namespace Holant.OneHot.Computable

open Holant.Complexity

/-- Uniform data-level preprocessing from the actual Boolean serialization.
Malformed records are rejected by the existing executable parser/validator. -/
def preprocess (signatureCount edgeLabelCount : ℕ) (arity : ℕ → ℕ) (bits : List Bool) :
    Option (List ℕ × List Graph.ParentRow) :=
  ((RawClosedNetwork.validatedEncoding signatureCount edgeLabelCount arity).decode bits).map fun r =>
    let g := r.1.graph r.2
    (g.roots.map Fin.val, g.parentTable)

/-- Parsing, endpoint recovery, component discovery and parent-table extraction
are connected to the real framed encoding, not to a supplied graph oracle. -/
theorem preprocess_encode {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)
    (h : r.WellFormed s b arity) :
    preprocess s b arity (RawClosedNetwork.encoding.encode r) =
      some (((r.graph h).roots.map Fin.val), (r.graph h).parentTable) := by
  unfold preprocess
  have hd := (RawClosedNetwork.validatedEncoding s b arity).decode_encode ⟨r, h⟩
  change (RawClosedNetwork.validatedEncoding s b arity).decode
    (RawClosedNetwork.encoding.encode r) = some ⟨r, h⟩ at hd
  rw [hd]
  rfl

end Holant.OneHot.Computable
