import Holant.Complexity.ClosedNetworkSemantics
import Mathlib.Data.List.OfFn

/-! Literal edge subdivision. Each original edge gets one ordered binary
vertex and two edges. Original vertex labels and local port order are retained.
This file contains syntax and incidence only; no machine-cost claim is made. -/
namespace Holant.Complexity.EdgeSubdivision
open RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

def outside (p : RawEndpoint) : RawEndpoint :=
  (2*p.1+(if p.2 then 1 else 0),p.2)

def inside (e : ℕ) : List RawEndpoint := [(2*e,true),(2*e+1,false)]

def oldVertex (v : RawVertex) : RawVertex := (v.1,v.2.map outside)

def edgeVertices (s : ℕ) (labels : List ℕ) : List RawVertex :=
  List.ofFn (fun e : Fin labels.length => (s+labels.get e,inside e.val))

def targetArity (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i<s then arity i else 2

def subdivide (s : ℕ) (r : RawClosedNetwork) : RawClosedNetwork where
  vertices := r.vertices.map oldVertex ++ edgeVertices s r.edges
  edges := List.replicate (2*r.edges.length) 0

@[simp] theorem vertices_length (s : ℕ) (r : RawClosedNetwork) :
    (subdivide s r).vertices.length=r.vertices.length+r.edges.length := by
  simp [subdivide,edgeVertices]

@[simp] theorem edges_length (s : ℕ) (r : RawClosedNetwork) :
    (subdivide s r).edges.length=2*r.edges.length := by simp [subdivide]

@[simp] theorem oldVertex_label (v : RawVertex) : (oldVertex v).1=v.1 := rfl
@[simp] theorem oldVertex_arity (v : RawVertex) : (oldVertex v).2.length=v.2.length := by
  simp [oldVertex]

theorem outside_injective : Function.Injective outside := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hb : b=c := congrArg Prod.snd h
  subst c
  have he := congrArg Prod.fst h
  cases b <;> simp [outside] at he <;> congr

def canonicalEnds (m : ℕ) : List RawEndpoint :=
  (List.ofFn (fun e : Fin m => [(e.val,false),(e.val,true)])).flatten

def outsideEnds (m : ℕ) : List RawEndpoint := (canonicalEnds m).map outside
def insideEnds (m : ℕ) : List RawEndpoint :=
  (List.ofFn (fun e : Fin m => inside e.val)).flatten

theorem canonicalEnds_succ (m : ℕ) :
    canonicalEnds (m+1)=canonicalEnds m++[(m,false),(m,true)] := by
  unfold canonicalEnds
  rw [List.ofFn_succ']
  simp only [Fin.coe_castSucc,Fin.val_last,List.concat_eq_append,List.flatten_append,
    List.flatten_cons,List.flatten_nil,List.append_nil]

theorem outsideEnds_succ (m : ℕ) :
    outsideEnds (m+1)=outsideEnds m++[(2*m,false),(2*m+1,true)] := by
  simp [outsideEnds,canonicalEnds_succ,outside]

theorem insideEnds_succ (m : ℕ) :
    insideEnds (m+1)=insideEnds m++inside m := by
  unfold insideEnds
  rw [List.ofFn_succ']
  simp only [Fin.coe_castSucc,Fin.val_last,List.concat_eq_append,List.flatten_append,
    List.flatten_cons,List.flatten_nil,List.append_nil]

theorem append_shuffle {α : Type*} (a b c d : List α) :
    ((a++b)++(c++d)).Perm ((a++c)++(b++d)) := by
  simpa only [List.append_assoc] using
    ((List.perm_append_comm (l₁:=b) (l₂:=c)).append_right d).append_left a

theorem subdivision_partition (m : ℕ) :
    (outsideEnds m++insideEnds m).Perm (canonicalEnds (2*m)) := by
  induction m with
  | zero => simp [outsideEnds,insideEnds,canonicalEnds]
  | succ m ih =>
    rw [outsideEnds_succ,insideEnds_succ]
    apply (append_shuffle _ _ _ _).trans
    have ht : ([(2*m,false),(2*m+1,true)]++inside m).Perm
        [(2*m,false),(2*m,true),(2*m+1,false),(2*m+1,true)] := by
      exact (List.perm_append_comm (l₁:=[(2*m+1,true)])
        (l₂:=[(2*m,true),(2*m+1,false)])).cons (2*m,false)
    have hh := ih.append ht
    simpa only [Nat.mul_add,Nat.mul_one,canonicalEnds_succ,inside,List.append_assoc,
      List.cons_append,List.nil_append] using hh

theorem subdivide_endpoints (s : ℕ) (r : RawClosedNetwork) :
    (subdivide s r).endpoints=r.endpoints.map outside++insideEnds r.edges.length := by
  simp only [RawClosedNetwork.endpoints,subdivide,List.map_append,List.flatten_append,
    List.map_map,oldVertex,Function.comp_def,edgeVertices,List.map_ofFn,insideEnds]
  rw [List.map_flatten]
  rw [List.map_map]
  rfl

theorem endpoint_permutation (s b : ℕ) (arity : ℕ → ℕ) (r : RawClosedNetwork)
    (hr : r.WellFormed s b arity) :
    (subdivide s r).endpoints.Perm (subdivide s r).expectedEndpoints := by
  rw [subdivide_endpoints]
  apply ((hr.2.2.map outside).append_right _).trans
  simpa only [RawClosedNetwork.expectedEndpoints,subdivide,List.length_replicate,
    outsideEnds,canonicalEnds,Fin.val_cast] using subdivision_partition r.edges.length

theorem subdivide_wellFormed (s b : ℕ) (arity : ℕ → ℕ) (r : RawClosedNetwork)
    (hr : r.WellFormed s b arity) :
    (subdivide s r).WellFormed (s+b) 1 (targetArity s arity) := by
  constructor
  · intro v
    have hv := List.get_mem (subdivide s r).vertices v
    change (subdivide s r).vertices.get v∈r.vertices.map oldVertex++edgeVertices s r.edges at hv
    rcases List.mem_append.mp hv with hv|hv
    · obtain ⟨u,hu,he⟩ := List.mem_map.mp hv
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hu
      rw [←he]
      have hi := hr.1 i
      refine ⟨by simpa using Nat.lt_add_right b hi.1,?_⟩
      rw [oldVertex_arity,oldVertex_label]
      unfold targetArity
      rw [if_pos hi.1]
      exact hi.2
    · obtain ⟨e,he⟩ := List.mem_ofFn.mp hv
      rw [←he]
      have heB := hr.2.1 e
      constructor
      · change s+r.edges.get e<s+b
        exact Nat.add_lt_add_left heB s
      · simp [inside,targetArity]
  · constructor
    · intro e
      simp [subdivide,List.get_eq_getElem]
    · exact endpoint_permutation s b arity r hr

end Holant.Complexity.EdgeSubdivision
