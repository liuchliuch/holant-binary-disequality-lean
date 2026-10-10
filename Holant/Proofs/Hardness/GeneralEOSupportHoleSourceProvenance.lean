import Holant.Proofs.Hardness.GeneralEONegativeSupportSource
import Holant.Proofs.Hardness.GeneralEOPinnedDescentPalette

/-! Literal embedding of an original support tensor into the descent palette.
The network, port map, ordered vertex records and edge records are unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSupportHoleSource
open Computability Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette
  (arity palette oldLabel pinLabel palette_old presentation pinnedValue)
end P
namespace N
export GeneralEONegativeSupportSource (Source select fromSelection)
end N
namespace C
export GeneralEONegativeTensorCore (arity graph template)
end C
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (D : N.Source G)

/-- The tensor graph is retained literally; every row keeps its old index. -/
def labels : Labelling D.graph.shape (s+1) 1 (P.arity (s:=s) (a:=a)) where
  vertex v := P.oldLabel (D.labels v)
  vertex_arity v := congrArg Sigma.fst (P.palette_old G (D.labels v))
  edge e := Fin.elim0 e

theorem exact : LabelledNetwork.Exact (P.palette G) D.graph (labels G D) :=
  fun v => P.palette_old G (D.labels v)

theorem native : ∀ e,D.graph.edge e=Signature.disequality := fun e => Fin.elim0 e

/-- Embedding into the larger palette changes no serialized incidence record. -/
theorem literal_template : (labels G D).template=C.template (a:=a) D.labels := rfl

theorem tensor_resources : D.graph.shape.vertices=D.copies ∧ D.graph.shape.edges=0 :=
  ⟨rfl,rfl⟩

theorem literal_labels (v : Fin D.copies) : (labels G D).vertex v=P.oldLabel (D.labels v) := rfl


/-- No added pin vertex occurs in the input tensor network. -/
theorem pin_count : LabelledNetwork.count (labels G D) (P.pinLabel (s:=s))=0 := by
  classical
  unfold LabelledNetwork.count
  apply Finset.sum_eq_zero
  intro v _
  have hn : (labels G D).vertex v≠P.pinLabel (s:=s) := by
    intro h
    have hv := congrArg Fin.val h
    change (D.labels v).val=s at hv
    exact (Nat.ne_of_lt (D.labels v).isLt) hv
  simp only [hn,ite_false]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSupportHoleSource
