import Holant.Complexity.GraphPreprocessing.CanonicalStability.Search

/-! Canonical BFS layers survive an ordered restriction retaining every actually
selected original parent edge. The proof follows those computed parents and
uses their shortest-layer specification, not a supplied replacement tree. -/
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable
variable (g h : Graph) (vs : h.Vertex ↪ g.Vertex) (es : h.Edge ↪o g.Edge)
    (he : ∀ d z, vs (h.endpoint d z) = g.endpoint (es d) z)
include he

/-- Every residual BFS step is an original BFS step on the same occurrence. -/
theorem reach_map (root : h.Vertex) : ∀ k v, v ∈ h.reach root k →
    vs v ∈ g.reach (vs root) k := by
  intro k
  induction k with
  | zero => intro v hv; simpa using congrArg vs (Finset.mem_singleton.mp hv)
  | succ k ih =>
    intro v hv
    rw [Graph.reach_succ,Graph.mem_round] at hv ⊢
    rcases hv with hv | ⟨⟨d,z⟩,hz,hp⟩
    · exact Or.inl (ih v hv)
    · exact Or.inr ⟨(es d,z),(he d z).symm.trans (congrArg vs hz),
        (he d (!z)) ▸ ih _ hp⟩

/-- An edge survives when its actual original ID occurs in the increasing
residual enumeration. This condition mentions the computed parentEnd itself. -/
def ParentsSurvive (root : g.Vertex) : Prop :=
  ∀ u : {u : g.Fiber root // u ≠ g.fiberRoot root},
    ∃ d : h.Edge, es d = (g.parentEnd root u).1

/-- All bounded BFS layers agree, not just eventual connectivity. -/
theorem reach_iff_of_parents_survive (root : h.Vertex)
    (hs : ParentsSurvive g h es (vs root)) :
    ∀ k v, v ∈ h.reach root k ↔ vs v ∈ g.reach (vs root) k := by
  intro k
  induction k with
  | zero => intro v; simp only [Graph.reach_zero,Finset.mem_singleton,vs.injective.eq_iff]
  | succ k ih =>
    intro v
    constructor
    · exact reach_map g h vs es he root (k+1) v
    · intro hv
      by_cases hr : v = root
      · subst v
        exact h.root_mem_reach root _
      let u : g.Fiber (vs root) :=
        ⟨vs v,(g.reach_iff _ _).mpr (g.reach_sound _ _ _ hv)⟩
      have hu : u ≠ g.fiberRoot (vs root) := by
        intro hh
        exact hr (vs.injective (congrArg Subtype.val hh))
      let q := g.parentEnd (vs root) ⟨u,hu⟩
      obtain ⟨d,hd⟩ := hs ⟨u,hu⟩
      have hq := g.parentEnd_spec (vs root) ⟨u,hu⟩
      change g.endpoint q.1 q.2 = vs v ∧ g.endpoint q.1 (!q.2) ∈
        g.reach (vs root) (g.depth (vs root) u - 1) at hq
      have hdepth : g.depth (vs root) u ≤ k+1 := g.depth_le_of_mem _ _ hv
      have hp : g.endpoint q.1 (!q.2) ∈ g.reach (vs root) k :=
        g.reach_mono _ (by omega) hq.2
      have hv' : h.endpoint d q.2 = v := by
        apply vs.injective
        rw [he,hd]
        exact hq.1
      apply (h.mem_round _ _).mpr
      refine Or.inr ⟨(d,q.2),hv',?_⟩
      apply (ih _).mpr
      rw [he,hd]
      exact hp

/-- The original component-fiber witness is obtained from the actual residual
reachability result, preserving the original vertex ID. -/
def fiberMap (root : h.Vertex) (v : h.Fiber root) : g.Fiber (vs root) :=
  ⟨vs v.val,(g.reach_iff _ _).mpr
    (g.reach_sound _ _ _ (reach_map g h vs es he root h.vertices v.val v.property))⟩

/-- First successful bounded-search rounds, hence BFS depths, are identical. -/
theorem depth_eq (root : h.Vertex) (hs : ParentsSurvive g h es (vs root))
    (v : h.Fiber root) : h.depth root v = g.depth (vs root) (fiberMap g h vs es he root v) := by
  apply Nat.le_antisymm
  · apply h.depth_le_of_mem
    exact (reach_iff_of_parents_survive g h vs es he root hs _ _).mpr (g.depth_mem _ _)
  · apply g.depth_le_of_mem
    exact reach_map g h vs es he root _ _ (h.depth_mem _ _)

end Holant.Complexity.GraphPreprocessing.CanonicalStability
