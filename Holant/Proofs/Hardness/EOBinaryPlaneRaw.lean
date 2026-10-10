import Holant.Proofs.Hardness.EOBinaryPlaneScanNat
import Holant.Proofs.Hardness.EOBinaryPlaneRecords
import Holant.Proofs.Hardness.BinaryCSPProgrammeCore
import Mathlib.Data.List.OfFn

/-! Typed semantics of the physical binary-CSP address tape. The original flat
edge list, including loops and repetitions, determines every native cycle port. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneRaw
open Holant Holant.Complexity
open scoped BigOperators
namespace P
export BinaryCSPProgrammeCore (Raw)
end P
namespace C
export EOBinaryPlaneCycles (Slot incidence)
end C
namespace S
export EOBinaryPlaneScan (next)
end S
namespace N
export EOBinaryPlaneScanNat (addresses next_value)
end N
set_option backward.isDefEq.respectTransparency false

def addresses (r : P.Raw) : List ℕ := r.edges.flatMap (fun e=>[e.1,e.2])

theorem addresses_length (r : P.Raw) : (addresses r).length=r.edges.length*2 := by
  simp [addresses,List.length_flatMap,List.map_const']

def scope (r : P.Raw) (hw : r.WellFormed) : C.Slot r.edges.length→Fin r.variables := fun s=>
  let p : Fin r.edges.length×Fin 2 := finProdFinEquiv.symm s
  let e := r.edges.get p.1
  if p.2=0 then ⟨e.1,(hw.1 e (List.get_mem _ _)).1⟩ else ⟨e.2,(hw.1 e (List.get_mem _ _)).2⟩

@[simp] theorem scope_zero (r : P.Raw) (hw : r.WellFormed) (v : Fin r.edges.length) :
    (scope r hw (C.incidence v 0)).val=(r.edges.get v).1 := by
  simp only [scope,C.incidence,Equiv.symm_apply_apply,ite_true]

@[simp] theorem scope_one (r : P.Raw) (hw : r.WellFormed) (v : Fin r.edges.length) :
    (scope r hw (C.incidence v 1)).val=(r.edges.get v).2 := by
  simp only [scope,C.incidence,Equiv.symm_apply_apply,one_ne_zero,ite_false]

theorem addresses_scope (r : P.Raw) (hw : r.WellFormed) : N.addresses (scope r hw)=addresses r := by
  unfold N.addresses
  rw [List.ofFn_mul]
  have hi (v : Fin r.edges.length) (j : Fin 2) (h : v.val*2+j.val<r.edges.length*2) :
      (⟨v.val*2+j.val,h⟩ : C.Slot r.edges.length)=C.incidence v j := by
    apply Fin.ext
    change v.val*2+j.val=j.val+2*v.val
    omega
  simp_rw [hi]
  have hrow (v : Fin r.edges.length) :
      (List.ofFn fun j : Fin 2=>(scope r hw (C.incidence v j)).val)=
      [(r.edges.get v).1,(r.edges.get v).2] := by
    simp [List.ofFn_succ]
  change (List.ofFn fun v : Fin r.edges.length=>
    List.ofFn fun j : Fin 2=>(scope r hw (C.incidence v j)).val).flatten=addresses r
  simp_rw [hrow]
  change (List.ofFn ((fun e : ℕ×ℕ=>[e.1,e.2]) ∘ r.edges.get)).flatten=addresses r
  rw [←List.map_ofFn,List.ofFn_get]
  rfl

def read {N : ℕ} (x : Fin N→Bool) (i : ℕ) : Bool := if h : i<N then x ⟨i,h⟩ else false

theorem read_at {N : ℕ} (x : Fin N→Bool) (i : Fin N) : read x i.val=x i := by
  simp [read,i.isLt]

def value {K : Type*} [CommSemiring K] (f : Signature K 2) (r : P.Raw) : K :=
  ∑x : Fin r.variables→Bool,(r.edges.map (fun e=>f ![read x e.1,read x e.2])).prod

theorem value_scope {K : Type*} [CommSemiring K] (f : Signature K 2) (r : P.Raw)
    (hw : r.WellFormed) : value f r=EOBinaryPlaneCSP.value f (scope r hw) := by
  unfold value EOBinaryPlaneCSP.value
  apply Finset.sum_congr rfl
  intro x _
  have hp : (r.edges.map (fun e=>f ![read x e.1,read x e.2])).prod=
      ∏v : Fin r.edges.length,f ![read x (r.edges.get v).1,read x (r.edges.get v).2] := by
    have h := congrArg (fun es : List (ℕ×ℕ)=>(es.map (fun e=>f ![read x e.1,read x e.2])).prod)
      (List.ofFn_get r.edges)
    simpa only [List.map_ofFn,List.prod_ofFn,Function.comp_def] using h.symm
  rw [hp]
  apply Finset.prod_congr rfl
  intro v _
  rw [←scope_zero r hw v,←scope_one r hw v,read_at,read_at]

def query (r : P.Raw) (hw : r.WellFormed) :
    Holant.LocalDrafts.Hardness.EightVertexNonexception.Source.TargetInput :=
  EOBinaryPlaneRecords.query (S.next (scope r hw))

theorem query_counts (r : P.Raw) (hw : r.WellFormed) :
    (query r hw).val.vertices.length=r.edges.length ∧
      (query r hw).val.edges.length=r.edges.length*2 := EOBinaryPlaneRecords.query_counts _

/-- Endpoints use exactly the natural-index successor emitted by the scan programme. -/
theorem query_rows (r : P.Raw) (hw : r.WellFormed) :
    (query r hw).val.vertices=List.ofFn (fun v : Fin r.edges.length=>(0,
      [((C.incidence v 0).val,false),(EOBinaryPlaneScanNat.next (addresses r) (C.incidence v 0).val,true),
       ((C.incidence v 1).val,false),(EOBinaryPlaneScanNat.next (addresses r) (C.incidence v 1).val,true)])) := by
  rw [query,EOBinaryPlaneRecords.query_vertices]
  unfold EOBinaryPlaneRecords.rows
  congr 1
  funext v
  rw [←N.next_value,←N.next_value,addresses_scope]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneRaw
