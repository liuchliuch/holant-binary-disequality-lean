import Holant.Complexity.BinaryInterpolation.Chains.Template
import Mathlib.Data.List.OfFn

/-! Explicit ordered records for variable-length chain compilation. The newest
edge has ID zero and all older IDs move up by one, matching the physical graph.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains
open Holant.Complexity.FixedGadgetSubstitution
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

def extendEndpoint : LocalEndpoint → LocalEndpoint
  | .inl i => if i = 0 then .inl 0 else .inr (0, false)
  | .inr p => .inr (p.1 + 1, p.2)

def extendRow (row : LocalVertex) : LocalVertex := (row.1, row.2.map extendEndpoint)

def explicitRow (label k i : ℕ) : LocalVertex :=
  (label, [if i = 0 then .inl 0 else .inr (k - i, true),
    if i = k then .inl 1 else .inr (k - 1 - i, false)])

def explicitTemplate (label edge k : ℕ) : Template where
  boundary := 2
  vertices := (List.range (k + 1)).map (explicitRow label k)
  edges := List.replicate k edge

@[simp] theorem explicitTemplate_vertices (label edge k : ℕ) :
    (explicitTemplate label edge k).vertices.length = k + 1 := by simp [explicitTemplate]

@[simp] theorem explicitTemplate_edges (label edge k : ℕ) :
    (explicitTemplate label edge k).edges.length = k := by simp [explicitTemplate]

theorem extend_explicitRow (label k i : ℕ) (hi : i ≤ k) :
    extendRow (explicitRow label k i) = explicitRow label (k + 1) i := by
  by_cases h0 : i = 0
  · subst i
    by_cases hk : k = 0
    · subst k; rfl
    · simp [extendRow, explicitRow, extendEndpoint, hk, Ne.symm hk]
      omega
  · have hs : i ≠ k + 1 := by omega
    by_cases hik : i = k
    · subst i
      simp [extendRow, explicitRow, extendEndpoint, h0]
    · simp [extendRow, explicitRow, extendEndpoint, h0, hik, hs]
      constructor <;> omega

theorem explicitTemplate_vertices_succ (label edge k : ℕ) :
    (explicitTemplate label edge (k + 1)).vertices =
      (explicitTemplate label edge k).vertices.map extendRow ++
        [(label, [.inr (0, true), .inl 1])] := by
  unfold explicitTemplate
  rw [List.range_succ]
  simp only [List.map_append, List.map_cons,
    List.map_nil, List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro i hi
    exact (extend_explicitRow label k i (Nat.lt_succ_iff.mp (List.mem_range.mp hi))).symm
  · simp [explicitRow]

end Holant.Complexity.BinaryInterpolation.Chains
