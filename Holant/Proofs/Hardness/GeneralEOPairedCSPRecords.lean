import Holant.Proofs.Hardness.GeneralEOPairedCSP
import Holant.Complexity.ClosedNetworkCompleteness

/-! Serialized arbitrary-arity original-family queries: original labels,
ordered port addresses, native-X edges, well-formedness, codec roundtrip and
exact partition value. No complexity or universal CSP-hardness premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPRecords
open Holant Holant.Tractable Holant.Complexity
namespace C
export GeneralEOPairedCSPCycles (Slot incidence shape network Covers compress)
end C
namespace S
export GeneralEOPairedCSPScan (next)
end S
set_option backward.isDefEq.respectTransparency false

variable {s N m : ℕ} {arity : ℕ→ℕ} (label : Fin s)
variable (p : OrientedPerfectPairing (arity label.val))

def labels (next : Equiv.Perm (C.Slot (N:=N) p)) : ClosedLabelling (C.shape p next) s 1 arity where
  vertex _ := label
  vertex_arity _ := rfl
  edge _ := 0

abbrev TargetInput := {r : RawClosedNetwork // r.WellFormed s 1 arity}

def query (next : Equiv.Perm (C.Slot (N:=N) p)) : TargetInput (s:=s) (arity:=arity) :=
  (labels label p next).validated

def rows (next : Equiv.Perm (C.Slot (N:=N) p)) : List RawVertex :=
  List.ofFn fun v : Fin N=>(label.val,List.ofFn fun k : Fin (arity label.val)=>
    let q := p.ports.symm k
    ((if q.2 then next (C.incidence p v q.1) else C.incidence p v q.1).val,q.2))

theorem query_vertices (next : Equiv.Perm (C.Slot (N:=N) p)) :
    (query label p next).val.vertices=rows label p next := by
  unfold query ClosedLabelling.validated ClosedLabelling.serialize rows
  congr 1

theorem query_edges (next : Equiv.Perm (C.Slot (N:=N) p)) :
    (query label p next).val.edges=List.replicate (N*p.count) 0 := by
  change List.ofFn (fun _ : Fin (N*p.count)=>(0 : Fin 1).val)=_
  simp

theorem query_counts (next : Equiv.Perm (C.Slot (N:=N) p)) :
    (query label p next).val.vertices.length=N ∧
      (query label p next).val.edges.length=N*p.count := by
  constructor <;> simp [query,ClosedLabelling.validated,C.shape]

theorem query_labels (next : Equiv.Perm (C.Slot (N:=N) p))
    (row : RawVertex) (hrow : row∈(query label p next).val.vertices) : row.1=label.val := by
  rw [query_vertices] at hrow
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hrow
  rfl

theorem query_roundtrip (next : Equiv.Perm (C.Slot (N:=N) p)) :
    (RawClosedNetwork.validatedEncoding s 1 arity).decode
      ((RawClosedNetwork.validatedEncoding s 1 arity).encode (query label p next))=
      some (query label p next) :=
  (RawClosedNetwork.validatedEncoding s 1 arity).decode_encode _

theorem query_denote {K : Type*} [CommSemiring K]
    (G : (i : Fin s)→Signature K (arity i.val))
    (next : Equiv.Perm (C.Slot (N:=N) p)) :
    ((query label p next).val.realize (query label p next).property G
      (fun _=>Signature.disequality)).denote Fin.elim0=
        (C.network p (G label) next).denote Fin.elim0 :=
  (labels label p next).denote_serialize G (fun _=>Signature.disequality)

/-- A validated, codec-compatible query over the unaltered original family.
All unqueried variable assignments are restored by the exact factor of two. -/
theorem query_value {K : Type*} [CommSemiring K]
    (G : (i : Fin s)→Signature K (arity i.val)) (hf : C.Covers p (G label))
    (scope : C.Slot (N:=N) p→Fin m) :
    GeneralEOPairedCSP.value p (C.compress p (G label)) scope=
      (2:K)^GeneralCSPUnused.unusedCount scope*
        ((query label p (S.next scope)).val.realize (query label p (S.next scope)).property G
          (fun _=>Signature.disequality)).denote Fin.elim0 := by
  rw [query_denote]
  exact GeneralEOPairedCSP.native_value p (G label) hf scope

/-- Literal emitted row addresses use the executable scan, in original port
order. In particular repeated variables and length-one occurrence cycles are
represented by ordinary graph loops where appropriate. -/
theorem query_scan_rows (scope : C.Slot (N:=N) p→Fin m) :
    (query label p (S.next scope)).val.vertices=List.ofFn (fun v : Fin N=>
      (label.val,List.ofFn fun k : Fin (arity label.val)=>
        let q := p.ports.symm k
        (if q.2 then GeneralEOPairedCSPScan.NatScan.next
          (GeneralEOPairedCSPScan.NatScan.addresses scope) (C.incidence p v q.1).val
          else (C.incidence p v q.1).val,q.2))) := by
  rw [query_vertices]
  unfold rows
  congr 1
  funext v
  congr 1
  apply congrArg List.ofFn
  funext k
  dsimp only
  rw [GeneralEOPairedCSPScan.NatScan.next_value]
  cases (p.ports.symm k).2 <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPRecords
