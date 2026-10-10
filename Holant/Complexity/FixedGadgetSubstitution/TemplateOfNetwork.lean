import Holant.Complexity.FixedGadgetSubstitution.WellFormed
import Holant.Complexity.ClosedNetworkSerialize

/-! Compile an actual ordered ordinary-boundary network into the fixed literal
replacement template. Its labels are original retained-family labels, not
analytic matrices or synthetic scalar resources. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
open scoped BigOperators

/-- Literal labels for every actual vertex and edge of the fixed source gadget. -/
structure Labelling {n : ℕ} (S : NetworkShape n) (s b : ℕ) (arity : ℕ → ℕ) where
  vertex : Fin S.vertices → Fin s
  vertex_arity : ∀ v, arity (vertex v).val = S.arity v
  edge : Fin S.edges → Fin b

namespace Labelling
variable {n s b : ℕ} {S : NetworkShape n} {arity : ℕ → ℕ}

def localEndpoint : (Fin n ⊕ (Fin S.edges × Bool)) → LocalEndpoint :=
  Sum.elim (fun i => .inl i.val) (fun p => .inr (p.1.val,p.2))

/-- Serialize every actual ordered gadget occurrence, including nullary ones. -/
def template (L : Labelling S s b arity) : Template where
  boundary := n
  vertices := List.ofFn (fun v : Fin S.vertices =>
    ((L.vertex v).val, List.ofFn (fun i : Fin (S.arity v) => localEndpoint (S.ports ⟨v,i⟩))))
  edges := List.ofFn (fun e : Fin S.edges => (L.edge e).val)

@[simp] theorem boundary (L : Labelling S s b arity) : L.template.boundary = n := rfl
@[simp] theorem vertices_length (L : Labelling S s b arity) :
    L.template.vertices.length = S.vertices := by simp [template]
@[simp] theorem edges_length (L : Labelling S s b arity) :
    L.template.edges.length = S.edges := by simp [template]

 theorem map_range_eq_ofFn {α : Type} (f : ℕ → α) (m : ℕ) :
    (List.range m).map f = List.ofFn (fun i : Fin m => f i.val) := by
  apply List.ext_getElem <;> simp

 theorem expected (L : Labelling S s b arity) : L.template.expectedEndpoints =
    List.ofFn (fun i : Fin n => (Sum.inl i.val : LocalEndpoint)) ++
      (List.ofFn (fun e : Fin S.edges =>
        [(Sum.inr (e.val,false) : LocalEndpoint),.inr (e.val,true)])).flatten := by
  simp only [Template.expectedEndpoints,template,List.length_ofFn,edgeEnds,
    List.map_flatMap,List.map_cons,List.map_nil,Nat.zero_add]
  rw [map_range_eq_ofFn]
  rw [List.flatMap, map_range_eq_ofFn]

/-- Multiplicity follows from the actual gadget's ordered port bijection. -/
 theorem endpoints_perm (L : Labelling S s b arity) :
    L.template.endpoints.Perm L.template.expectedEndpoints := by
  letI : BEq LocalEndpoint := instBEqOfDecidableEq
  apply List.perm_iff_count.mpr
  intro p
  have hsum := S.ports.sum_comp
    (fun q : Fin n ⊕ (Fin S.edges × Bool) => if localEndpoint q = p then (1 : ℕ) else 0)
  simp only [Fintype.sum_sigma,Fintype.sum_sum_type,Fintype.sum_prod_type] at hsum
  rw [expected]
  simpa only [template,Template.endpoints,List.map_ofFn,List.count_flatten,
    List.sum_ofFn,ClosedLabelling.count_ofFn,List.count_append,List.count_cons,
    List.count_nil,Fintype.sum_bool,localEndpoint,beq_iff_eq,Nat.zero_add,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Nat.add_zero,Nat.add_comm]
    using hsum

 theorem wellFormed (L : Labelling S s b arity) : L.template.WellFormed s b arity := by
  refine ⟨?_,?_,L.endpoints_perm⟩
  · intro row hrow
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hrow
    exact ⟨(L.vertex v).isLt,by simpa using (L.vertex_arity v).symm⟩
  · intro label hlabel
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hlabel
    exact (L.edge e).isLt

end Labelling
end Holant.Complexity.FixedGadgetSubstitution
