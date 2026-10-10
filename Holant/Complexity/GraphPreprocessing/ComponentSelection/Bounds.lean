import Holant.Complexity.GraphPreprocessing.ComponentSelection.RawRoots
import Holant.Complexity.GraphPreprocessing.ComponentSelection.RawSurplus

/-! Direct original-bit output bounds for consumers of physical component
selection. These sharpen the generic composed-machine output polynomials. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection
open Computability OriginalCoefficient
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem unaryList_length (xs : List ℕ) (N : ℕ) (h : ∀x∈xs,x≤N) :
    (framedListEncode UnaryBinary.unaryEncoding xs).length≤xs.length*(2*N+2)+1 := by
  induction xs with
  | nil => simp [framedListEncode]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [framedListEncode,List.length_cons,List.length_append,Holant.Algebraic.frame_length,
      UnaryBinary.unaryEncoding,List.length_replicate]
    simp only [UnaryBinary.unaryEncoding] at ht
    nlinarith

theorem RawRoots.output_length (x : RawRoots.Input s b arity) :
    (RawRoots.outputEncoding.encode (RawRoots.value x)).length≤
      2*((RawClosedNetwork.encoding.encode x.val).length+1)^2+1 := by
  let N := (RawClosedNetwork.encoding.encode x.val).length
  have hc := x.val.counts_le_encoded_length
  have hv : x.val.vertices.length≤N := by omega
  have h := unaryList_length (RawRoots.value x) N (by
    intro a ha
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
    have hi := v.isLt
    change v.val<x.val.vertices.length at hi
    omega)
  have hl : (RawRoots.value x).length≤N := by
    have hr := (x.val.graph x.property).roots_length_le
    simp only [RawRoots.value,List.length_map]
    exact hr.trans hv
  have hm := Nat.mul_le_mul_right (2*N+2) hl
  change (framedListEncode UnaryBinary.unaryEncoding (RawRoots.value x)).length≤2*(N+1)^2+1
  nlinarith

theorem RawSurplus.edges_length (x : RawSurplus.Input s b arity) :
    (RawSurplus.edges x).length≤x.1.val.edges.length := by
  have h := surplus_length_le (x.1.val.graph x.1.property) ((x.1.val.graph x.1.property).label x.2)
  rw [x.1.val.graph_edges x.1.property] at h
  simpa only [RawSurplus.edges,List.length_map] using h
theorem RawSurplus.edge_lt (x : RawSurplus.Input s b arity) (e : ℕ) (h : e∈RawSurplus.edges x) :
    e<x.1.val.edges.length := by
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp h
  exact lt_of_lt_of_le q.isLt (Nat.le_of_eq (x.1.val.graph_edges x.1.property))
theorem RawSurplus.unicycle_lt (x : RawSurplus.Input s b arity) (e : ℕ)
    (h : RawSurplus.value x=.unicycle e) : e<x.1.val.edges.length := by
  obtain ⟨q,hq,_⟩ := RawSurplus.unicycle_unused x e h
  rw [←hq]
  exact q.isLt
theorem RawSurplus.unicycle_unused_id (x : RawSurplus.Input s b arity) (e : ℕ)
    (h : RawSurplus.value x=.unicycle e) :
    ∀ v : Fin x.1.val.vertices.length, ∀q∈((x.1.val.graph x.1.property).parentRow v).parent,q.1≠e := by
  obtain ⟨q,hq,hu⟩ := RawSurplus.unicycle_unused x e h
  simpa only [hq] using hu
theorem RawSurplus.output_length (x : RawSurplus.Input s b arity) :
    (ClassifyList.outputEncoding.encode (RawSurplus.value x)).length≤
      (RawClosedNetwork.encoding.encode x.1.val).length+2 := by
  have hc := x.1.val.counts_le_encoded_length
  cases h : RawSurplus.value x with
  | tree => simp [ClassifyList.outputEncoding]
  | dense => simp [ClassifyList.outputEncoding]
  | unicycle e =>
    obtain ⟨q,hq,_⟩ := RawSurplus.unicycle_unused x e h
    have hi := q.isLt
    simp only [ClassifyList.outputEncoding,List.length_cons,List.length_replicate]
    omega
end Holant.Complexity.GraphPreprocessing.ComponentSelection
