import Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalFamily

/-! Exact original-Γ size accounting after eliminating every temporary B.
If the fixed macro has V vertices and E edges, the sample t=k+1 has
|Vout|+m=|Vin|+Vtm and |Eout|=|Ein|+km+Etm. Thus the actual Γ queries retain
the source's quadratic/cubic added-vertex bounds with fixed macro constants.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalFamily
open FixedGadgetSubstitution RawClosedNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem macro_vertex_sum {s : ℕ} (arity : ℕ → ℕ) (g : Template) (rs : List RawVertex)
    (hb : ∀ r ∈ rs, r.1 < s + 1) :
    (rs.map (fun r => (Adjoin.templates s arity g r.1).vertices.length)).sum +
      (rs.filter (fun r => r.1 == s)).length =
      rs.length + g.vertices.length * (rs.filter (fun r => r.1 == s)).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := hb r (by simp)
    have ht := ih (fun x hx => hb x (by simp [hx]))
    by_cases h : r.1 = s
    · simp [Adjoin.templates,h,Nat.mul_add] at ht ⊢
      omega
    · have hlt : r.1 < s := by omega
      simp [Adjoin.templates,h,hlt,identityTemplate] at ht ⊢
      omega

theorem macro_edge_sum {s : ℕ} (arity : ℕ → ℕ) (g : Template) (rs : List RawVertex)
    (hb : ∀ r ∈ rs, r.1 < s + 1) :
    (rs.map (fun r => (Adjoin.templates s arity g r.1).edges.length)).sum =
      g.edges.length * (rs.filter (fun r => r.1 == s)).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := hb r (by simp)
    have ht := ih (fun x hx => hb x (by simp [hx]))
    by_cases h : r.1 = s
    · simp [Adjoin.templates,h,Nat.mul_add] at ht ⊢
      omega
    · have hlt : r.1 < s := by omega
      simp [Adjoin.templates,h,hlt,identityTemplate] at ht ⊢
      omega

variable {s b : ℕ} (arity : ℕ → ℕ) (g : Template) (hg : g.WellFormed s b arity)
variable (hbinary : g.boundary = 2) (edge : Fin b)

theorem value_vertex_balance (x : Input (s:=s) (b:=b) arity g) :
    (value arity g hg hbinary edge x).val.vertices.length + occurrences s x.1.val =
      x.1.val.vertices.length + g.vertices.length * ((x.2.val + 1) * occurrences s x.1.val) := by
  have hb : ∀ r ∈ (intermediate arity g hbinary edge x).val.vertices, r.1 < s + 1 := by
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
    exact ((intermediate arity g hbinary edge x).property.1 i).1
  have h := macro_vertex_sum arity g (intermediate arity g hbinary edge x).val.vertices hb
  rw [←replace_vertex_count] at h
  change (value arity g hg hbinary edge x).val.vertices.length +
    occurrences s (intermediate arity g hbinary edge x).val =
    (intermediate arity g hbinary edge x).val.vertices.length +
      g.vertices.length * occurrences s (intermediate arity g hbinary edge x).val at h
  rw [exponent_exact] at h
  have hv : (intermediate arity g hbinary edge x).val.vertices.length =
      x.1.val.vertices.length + x.2.val * occurrences s x.1.val :=
    Occurrence.raw_vertices (s + 1) b (macroArity (s:=s) arity g) s s edge.val (x.2.val,x.1)
  rw [hv] at h
  simp only [Nat.add_mul,Nat.one_mul] at h ⊢
  omega

theorem value_edges (x : Input (s:=s) (b:=b) arity g) :
    (value arity g hg hbinary edge x).val.edges.length =
      x.1.val.edges.length + x.2.val * occurrences s x.1.val +
        g.edges.length * ((x.2.val + 1) * occurrences s x.1.val) := by
  have hb : ∀ r ∈ (intermediate arity g hbinary edge x).val.vertices, r.1 < s + 1 := by
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
    exact ((intermediate arity g hbinary edge x).property.1 i).1
  change (replace (Adjoin.templates s arity g) (intermediate arity g hbinary edge x).val).edges.length = _
  rw [replace_edge_count,macro_edge_sum arity g _ hb]
  change (intermediate arity g hbinary edge x).val.edges.length +
    g.edges.length * occurrences s (intermediate arity g hbinary edge x).val = _
  rw [exponent_exact]
  have he : (intermediate arity g hbinary edge x).val.edges.length =
      x.1.val.edges.length + x.2.val * occurrences s x.1.val :=
    Occurrence.raw_edges (s + 1) b (macroArity (s:=s) arity g) s s edge.val (x.2.val,x.1)
  rw [he]

theorem added_vertices_le (x : Input (s:=s) (b:=b) arity g) :
    (value arity g hg hbinary edge x).val.vertices.length - x.1.val.vertices.length ≤
      g.vertices.length * ((occurrences s x.1.val + 1) * occurrences s x.1.val) := by
  have hv := value_vertex_balance arity g hg hbinary edge x
  have hk := BoundedQueries.index_le _ _ _ _ x
  have ht := Nat.mul_le_mul_right (occurrences s x.1.val) (Nat.add_le_add_right hk 1)
  have hm := Nat.mul_le_mul_left g.vertices.length ht
  omega

theorem all_added_vertices_le
    (r : FixedGadgetSubstitution.Compiler.Input (s + 1) b (macroArity (s:=s) arity g)) :
    (∑ k : Fin (occurrences s r.val + 1),
      ((value arity g hg hbinary edge ⟨r,k⟩).val.vertices.length - r.val.vertices.length)) ≤
      (occurrences s r.val + 1) * (g.vertices.length * ((occurrences s r.val + 1) * occurrences s r.val)) := by
  calc
    _ ≤ ∑ _k : Fin (occurrences s r.val + 1),
        g.vertices.length * ((occurrences s r.val + 1) * occurrences s r.val) := by
      apply Finset.sum_le_sum
      intro k _
      exact added_vertices_le arity g hg hbinary edge ⟨r,k⟩
    _ = _ := by simp

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalFamily
