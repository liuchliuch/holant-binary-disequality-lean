import Holant.Proofs.Hardness.EOBinaryPlaneOrient
import Holant.Proofs.Hardness.OriginalPortAccess

/-! Literal original-field transport for the plane normalization and compressed
argument complements. The actual row writer, original edge order, field embedding,
answer retraction, and length-controlled physical programme are reused intact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePortAccess
open Holant Holant.Algebraic Holant.Complexity
namespace C
export EOBinaryPlaneCore (normalized compress lift normalized_lift)
end C
namespace F
export EOBinaryPlaneOrient (ports signsFor oriented lift_flip)
end F
namespace A
export OriginalPortAccess (normalized normalized_algebraic controlled query query_rows query_edges
  query_vertex_count field_le embedding embedding_value answer answerComputes)
end A
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation TargetInput targetEncoding targetValue)
end O
set_option backward.isDefEq.respectTransparency false

def ports (plane : Fin 6) (missing : Fin 2→Bool) : Equiv.Perm (Fin 4) :=
  (FiveSupportEOOrdering.orderAt plane).trans (F.ports (F.signsFor missing))

def output {K : Type} (M : Signature K 4) (plane : Fin 6) (missing : Fin 2→Bool) : Signature K 4 :=
  OriginalPortAccess.normalized M (ports plane missing)

theorem output_lift {K : Type} [Field K] (M : Signature K 4)
    (he : DenseEOUnitLocal.EOSupport M) (plane : Fin 6)
    (h0 : FiveSupportEOOrdering.middleCoeff M plane=0)
    (h1 : FiveSupportEOOrdering.middleCoeff M (5-plane)=0) (missing : Fin 2→Bool) :
    output M plane missing=C.lift (F.oriented (C.compress (C.normalized M plane)) missing) := by
  change Tensor.reindex (F.ports (F.signsFor missing)) (C.normalized M plane)=_
  rw [←C.normalized_lift M he plane h0 h1,F.lift_flip,EOBinaryPlaneCore.compress_lift]
  rfl

variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (plane : Fin 6) (missing : Fin 2→Bool)

abbrev output_algebraic := A.normalized_algebraic M halg (ports plane missing)

/-- Actual physical reduction to the original input and its unchanged codec. -/
abbrev source := A.controlled M halg (ports plane missing)

abbrev query := A.query M (ports plane missing)

theorem query_rows (r : O.TargetInput) :
    (query M plane missing r).val.vertices=
      r.val.vertices.map (OriginalPortAccess.permuteRow (ports plane missing)) :=
  A.query_rows M (ports plane missing) r

theorem query_edges (r : O.TargetInput) : (query M plane missing r).val.edges=r.val.edges :=
  A.query_edges M (ports plane missing) r

theorem query_vertex_count (r : O.TargetInput) :
    (query M plane missing r).val.vertices.length=r.val.vertices.length :=
  A.query_vertex_count M (ports plane missing) r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePortAccess
