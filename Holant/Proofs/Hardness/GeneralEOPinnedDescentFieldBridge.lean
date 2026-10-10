import Holant.Proofs.Hardness.GeneralEOPinnedDescentLift
import Holant.Proofs.Algorithms.FieldTransport

/-! A labelled ambient macro can be queried using its own generated field and
compiled to original-family-plus-pin graphs in the unchanged original field.
The answer conversion is the actual rational-linear retraction program. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentFieldBridge
open Computability Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open FixedGadgetSubstitution ExactSignatureTables BinaryCompose
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue target_exact)
end O
namespace P
export GeneralEOPinnedDescentPalette (arity palette pinned presentation pinnedValue)
end P
namespace L
export GeneralEOPinnedDescentLift (lift labels exact native denote_lift)
end L
namespace A
export GeneralEOPinnedDescentAccess
  (sourceValue sourceTables tables query queryComputes query_counts query_value)
end A
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (S : Network AlgebraicComplex n)
variable (SL : Labelling S.shape (s+1) 1 (P.arity (s:=s) (a:=a)))
variable (he : LabelledNetwork.Exact (P.palette G) S SL)
variable (hn : ∀e,S.edge e=Signature.disequality)

def macroFamily (_ : Fin 1) : Signature AlgebraicComplex n := S.denote
abbrev macroField := O.originalField (arity:=fun _ => n) (macroFamily S)
abbrev macroPresentation := O.originalPresentation (arity:=fun _ => n) (macroFamily S)
abbrev macroValue := O.originalValue (arity:=fun _ => n) (macroFamily S)
local instance macroAlgebra : Algebra ℚ (macroField S) := (macroField S).algebra'

include he hn in
theorem field_le : macroField S≤O.originalField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  change S.denote x∈O.originalField G
  rw [←L.denote_lift G S SL he hn x]
  exact ((L.lift G S SL).denote x).property

def embedding : macroField S →ₐ[ℚ] O.originalField G :=
  IntermediateField.inclusion (field_le G S SL he hn)

theorem embedding_value (x : macroField S) :
    (embedding G S SL he hn x : AlgebraicComplex)=x :=
  IntermediateField.coe_inclusion (field_le G S SL he hn) x

include he hn in
theorem lifted_source_ambient (q : Input 1 1 (fun _ => n)) :
    ((A.sourceValue (P.presentation G) (L.lift G S SL) q : O.originalField G) : AlgebraicComplex)=
      (q.val.realize q.property (macroFamily S) (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  rw [A.sourceValue,ExactSignatureTables.evaluate_eq_decoded]
  simp only [A.sourceTables,LinearEquiv.apply_symm_apply]
  change (O.originalField G).subtype _=_
  rw [←Network.denote_map (O.originalField G).subtype]
  apply congrArg (fun N : Network AlgebraicComplex 0 => N.denote Fin.elim0)
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact L.denote_lift G S SL he hn x
  · funext e u v
    cases u <;> cases v <;> rfl

include he hn in
theorem lifted_source_value (q : Input 1 1 (fun _ => n)) :
    A.sourceValue (P.presentation G) (L.lift G S SL) q=
      embedding G S SL he hn (macroValue S q) := by
  apply Subtype.ext
  rw [lifted_source_ambient G S SL he hn,embedding_value,O.target_exact]

def query := A.query (L.lift G S SL) (L.labels G S SL)
def answer := (embedding G S SL he hn).toLinearMap.leftInverse

def answerComputes : Computes (P.presentation G).encoding (macroPresentation S).encoding
    (answer G S SL he hn) :=
  Holant.LocalDrafts.MainChain.FieldCodec.retractComputes
    (macroPresentation S) (P.presentation G) (embedding G S SL he hn)

include he hn in
theorem query_value (q : Input 1 1 (fun _ => n)) :
    P.pinnedValue G (query G S SL q)=embedding G S SL he hn (macroValue S q) := by
  exact (A.query_value (P.presentation G) (P.pinned G) (L.lift G S SL) (L.labels G S SL)
    (L.exact G S SL) (L.native G S SL) q).trans (lifted_source_value G S SL he hn q)

/-- Actual macro compiler followed by the implemented field retraction.
No equality between the macro field and the original field is assumed. -/
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 1 1 (fun _ => n)) (macroPresentation S).encoding
    (RawClosedNetwork.validatedEncoding (s+1) 1 (P.arity (s:=s) (a:=a))) (P.presentation G).encoding
    (macroValue S) (P.pinnedValue G) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (A.queryComputes (L.lift G S SL) (L.labels G S SL))
    (answerComputes G S SL he hn) ((A.tables (P.presentation G) (P.pinned G)).outputBound (P.presentation G))
    (macroValue S) (fun q => by
      change macroValue S q=answer G S SL he hn (P.pinnedValue G (query G S SL q))
      rw [query_value G S SL he hn]
      exact (Holant.LocalDrafts.MainChain.FieldCodec.retract_embedding (embedding G S SL he hn) _).symm)

theorem query_counts (q : Input 1 1 (fun _ => n)) :
    (query G S SL q).val.vertices.length=q.val.vertices.length*S.shape.vertices ∧
    (query G S SL q).val.edges.length=q.val.edges.length+q.val.vertices.length*S.shape.edges :=
  A.query_counts (L.lift G S SL) (L.labels G S SL) q

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentFieldBridge
