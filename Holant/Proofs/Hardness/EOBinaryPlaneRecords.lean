import Holant.Proofs.Hardness.EOBinaryPlaneCycles
import Holant.Complexity.ClosedNetworkCompleteness
import Holant.Proofs.Reductions.EightVertexNonexception.Source

/-! Original-M closed query records for the opposite-pair binary CSP bridge.
Labels, ordered ports, native-X edges, validity, codec roundtrip, and the
original coefficient-field answer are all retained. No machine-time or
counting-hardness theorem is asserted by this semantic compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneRecords
open Holant Holant.Algebraic Holant.Complexity
namespace C
export EOBinaryPlaneCycles (Slot incidence shape network value denote_lift)
end C
namespace B
export EOBinaryPlaneCore (compress lift lift_compress)
end B
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation TargetInput targetEncoding targetValue target_value_exact)
end O
set_option backward.isDefEq.respectTransparency false

/-- One literal original-M vertex label and one literal native-X edge label. -/
def labels {n : ℕ} (next : Equiv.Perm (C.Slot n)) : ClosedLabelling (C.shape next) 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge _ := 0

def query {n : ℕ} (next : Equiv.Perm (C.Slot n)) : O.TargetInput := (labels next).validated

def rows {n : ℕ} (next : Equiv.Perm (C.Slot n)) : List RawVertex :=
  List.ofFn fun v : Fin n=>(0,[(C.incidence v 0).val |> fun e=>(e,false),
    ((next (C.incidence v 0)).val,true),(C.incidence v 1).val |> fun e=>(e,false),
    ((next (C.incidence v 1)).val,true)])

theorem query_vertices {n : ℕ} (next : Equiv.Perm (C.Slot n)) :
    (query next).val.vertices=rows next := by
  unfold query ClosedLabelling.validated ClosedLabelling.serialize rows
  congr 1

theorem query_edges {n : ℕ} (next : Equiv.Perm (C.Slot n)) :
    (query next).val.edges=List.replicate (n*2) 0 := by
  change List.ofFn (fun _ : Fin (n*2)=>(0 : Fin 1).val)=_
  simp

theorem query_counts {n : ℕ} (next : Equiv.Perm (C.Slot n)) :
    (query next).val.vertices.length=n ∧ (query next).val.edges.length=n*2 := by
  constructor <;> simp [query,ClosedLabelling.validated,C.shape]

theorem query_roundtrip {n : ℕ} (next : Equiv.Perm (C.Slot n)) :
    O.targetEncoding.decode (O.targetEncoding.encode (query next))=some (query next) :=
  O.targetEncoding.decode_encode _

theorem query_denote {K : Type*} [CommSemiring K] {n : ℕ}
    (M : Signature K 4) (next : Equiv.Perm (C.Slot n)) :
    ((query next).val.realize (query next).property (fun _=>M)
      (fun _=>Signature.disequality)).denote Fin.elim0=(C.network M next).denote Fin.elim0 := by
  exact (labels next).denote_serialize (fun _=>M) (fun _=>Signature.disequality)

theorem query_lift {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Signature K 2) (next : Equiv.Perm (C.Slot n)) :
    ((query next).val.realize (query next).property (fun _=>B.lift f)
      (fun _=>Signature.disequality)).denote Fin.elim0=C.value f next :=
  (query_denote _ next).trans (C.denote_lift f next)

/-- The answer from the original field is exactly the binary partition sum.
No equality of encodings or enlarged coefficient field is used. -/
theorem original_value {L : Type} [Field L] [Algebra ℚ L] {n : ℕ}
    (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x))
    (he : DenseEOUnitLocal.EOSupport M)
    (hb : (Holant.LocalDrafts.Hardness.EightVertexNonexception.entries M).b=0)
    (hy : (Holant.LocalDrafts.Hardness.EightVertexNonexception.entries M).y=0)
    (next : Equiv.Perm (C.Slot n)) :
    ((O.targetValue M halg (query next) : O.field M) : L)=C.value (B.compress M) next := by
  rw [O.target_value_exact,query_denote,←B.lift_compress M he hb hy,C.denote_lift]
  rw [EOBinaryPlaneCore.compress_lift]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneRecords
