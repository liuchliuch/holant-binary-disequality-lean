import Holant.Complexity.EdgeSubdivision.Raw
import Holant.Complexity.EdgeSubdivision.Finite

/-! The compiler's literal vertex/edge enumeration and ordered port lookup. -/
namespace Holant.Complexity.EdgeSubdivision
open RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
variable (s : ℕ) (r : RawClosedNetwork)

def vertexOrder : Fin (subdivide s r).vertices.length ≃
    (Fin r.vertices.length ⊕ Fin r.edges.length) :=
  (finCongr (vertices_length s r)).trans finSumFinEquiv.symm

def edgeOrder : Fin (subdivide s r).edges.length ≃ (Fin r.edges.length×Bool) :=
  (finCongr ((edges_length s r).trans (Nat.mul_comm _ _))).trans
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv))

@[simp] theorem vertexOrder_old (v : Fin r.vertices.length) :
    ((vertexOrder s r).symm (.inl v)).val=v.val := rfl
@[simp] theorem vertexOrder_new (e : Fin r.edges.length) :
    ((vertexOrder s r).symm (.inr e)).val=r.vertices.length+e.val := rfl
@[simp] theorem edgeOrder_val (e : Fin r.edges.length) (b : Bool) :
    ((edgeOrder s r).symm (e,b)).val=2*e.val+(if b then 1 else 0) := by
  cases b <;> simp [edgeOrder,finTwoEquiv,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

def localVertex : (Fin r.vertices.length ⊕ Fin r.edges.length) → RawVertex :=
  Sum.elim (fun v => oldVertex (r.vertices.get v))
    (fun e => (s+r.edges.get e,inside e.val))

theorem vertex_record (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    (subdivide s r).vertices.get ((vertexOrder s r).symm p)=localVertex s r p := by
  cases p with
  | inl v => simp [subdivide,List.get_eq_getElem,localVertex,vertexOrder]
  | inr e => simp [subdivide,List.get_eq_getElem,localVertex,vertexOrder,edgeVertices]

theorem vertex_label (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    ((subdivide s r).vertices.get ((vertexOrder s r).symm p)).1=(localVertex s r p).1 :=
  congrArg Prod.fst (vertex_record s r p)

variable {b : ℕ} {arity : ℕ → ℕ}
variable (hr : r.WellFormed s b arity)

abbrev queryValid := subdivide_wellFormed s b arity r hr

def queryPort (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (i : Fin (targetArity s arity (localVertex s r p).1)) :
    (subdivide s r).Ports (targetArity s arity) :=
  ⟨(vertexOrder s r).symm p,
    Fin.cast (congrArg (targetArity s arity) (vertex_label s r p).symm) i⟩

theorem query_portEndpoint (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (i : Fin (targetArity s arity (localVertex s r p).1)) :
    (subdivide s r).portEndpoint (queryValid s r hr) (queryPort s r p i) =
      (localVertex s r p).2.get
        ⟨i.val,by
          have h := (queryValid s r hr).1 ((vertexOrder s r).symm p)
          rw [vertex_record] at h
          rw [h.2]
          exact i.isLt⟩ := by
  simp only [RawClosedNetwork.portEndpoint,queryPort,List.get_eq_getElem,Fin.val_cast]
  exact getElem_congr_coll (congrArg Prod.snd (vertex_record s r p))

def localArity : (Fin r.vertices.length ⊕ Fin r.edges.length) → ℕ :=
  Sum.elim (fun v => arity (r.vertices.get v).1) (fun _ => 2)

include hr in
theorem localArity_eq (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    targetArity s arity (localVertex s r p).1 = localArity (arity:=arity) r p := by
  cases p with
  | inl v =>
    have hv : r.vertices[v.val].1 < s := (hr.1 v).1
    simp [localVertex,oldVertex,targetArity,localArity,hv]
  | inr e => simp [localVertex,targetArity,localArity]

def orderedPort (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (i : Fin (localArity (arity:=arity) r p)) : (subdivide s r).Ports (targetArity s arity) :=
  queryPort s r p (Fin.cast (localArity_eq s r hr p).symm i)

def attachment (p : Fin r.vertices.length ⊕ Fin r.edges.length) :
    Fin (localArity (arity:=arity) r p) → ((Fin r.edges.length×Bool)×Bool) :=
  match p with
  | .inl v => fun i => let q := r.route hr ⟨v,i⟩; (q,q.2)
  | .inr e => fun i => ((e,finTwoEquiv i),!(finTwoEquiv i))

theorem attachment_numeric (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (i : Fin (localArity (arity:=arity) r p)) :
    (subdivide s r).portEndpoint (queryValid s r hr) (orderedPort s r hr p i) =
      (((edgeOrder s r).symm (attachment s r hr p i).1).val,
        (attachment s r hr p i).2) := by
  unfold orderedPort
  rw [query_portEndpoint s r hr]
  cases p with
  | inl v =>
    simp only [localVertex,Sum.elim_inl,oldVertex,List.get_eq_getElem,Fin.val_cast,
      List.getElem_map,attachment]
    rw [edgeOrder_val]
    rfl
  | inr e =>
    change Fin 2 at i
    fin_cases i <;>
      simp [localVertex,localArity,inside,List.get_eq_getElem,attachment,finTwoEquiv,edgeOrder_val]

theorem query_route (p : Fin r.vertices.length ⊕ Fin r.edges.length)
    (i : Fin (localArity (arity:=arity) r p)) :
    (subdivide s r).route (queryValid s r hr) (orderedPort s r hr p i) =
      ((edgeOrder s r).symm (attachment s r hr p i).1,
        (attachment s r hr p i).2) := by
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Prod.fst (attachment_numeric s r hr p i)
  · change ((subdivide s r).portEndpoint (queryValid s r hr) (orderedPort s r hr p i)).2 = _
    exact congrArg Prod.snd (attachment_numeric s r hr p i)

end Holant.Complexity.EdgeSubdivision
