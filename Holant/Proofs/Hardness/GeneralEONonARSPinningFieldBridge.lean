import Holant.Proofs.Hardness.GeneralEOPinnedDescentAccess
import Holant.Proofs.Hardness.GeneralEOBinaryPinSource
import Holant.Proofs.Algorithms.FieldTransport

/-! An unpinned original-labelled macro compiles into the exact original
dictionary. Its generated field is included in the original field by the
physical graph, and the actual rational-linear answer programme retracts it.
No pin-augmented target, field equality, or assumed reduction is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningFieldBridge
open Computability Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open FixedGadgetSubstitution ExactSignatureTables BinaryCompose
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue target_exact)
end O
namespace A
export GeneralEOPinnedDescentAccess
  (sourceValue sourceTables tables query queryComputes query_counts query_value)
end A
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
abbrev original := GeneralEOBinaryPinSource.original G
abbrev presentation := O.originalPresentation G
variable (S : Network AlgebraicComplex n) (SL : Labelling S.shape s 1 a)
variable (he : LabelledNetwork.Exact G S SL) (hn : ∀e,S.edge e=Signature.disequality)

def lift : Network (O.originalField G) n :=
  SL.sourceNetwork (original G) (fun _ : Fin 1 => Signature.disequality)

def labels : Labelling (lift G S SL).shape s 1 a := SL

private theorem exact_cast {K : Type} {m k : ℕ} (h : m=k) (f : Signature K m) :
    (⟨m,f⟩ : AnySignature K)=⟨k,fun x => f (fun i => x (Fin.cast h i))⟩ := by
  subst k
  rfl

theorem exact : LabelledNetwork.Exact (original G) (lift G S SL) (labels G S SL) := by
  intro v
  exact exact_cast (SL.vertex_arity v) (original G (SL.vertex v))

theorem native : ∀e,(lift G S SL).edge e=Signature.disequality := fun _ => rfl

private theorem apply_exact {K : Type} {m k : ℕ} (f : Signature K m) (g : Signature K k)
    (h : (⟨m,f⟩ : AnySignature K)=⟨k,g⟩) (hk : m=k) (x : Fin k → Bool) :
    f (fun i => x (Fin.cast hk i))=g x := by
  cases h
  rfl

include he hn in
theorem map_lift : (lift G S SL).map (O.originalField G).subtype=S := by
  unfold Network.map lift Labelling.sourceNetwork
  congr 1
  · funext v x
    exact apply_exact _ _ (he v) (SL.vertex_arity v) x
  · funext e u v
    rw [hn e]
    cases u <;> cases v <;> rfl

include he hn in
theorem denote_lift (x : Fin n → Bool) :
    ((lift G S SL).denote x : AlgebraicComplex)=S.denote x := by
  change (O.originalField G).subtype ((lift G S SL).denote x)=_
  rw [←Network.denote_map (O.originalField G).subtype,map_lift G S SL he hn]

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
  rw [←denote_lift G S SL he hn x]
  exact ((lift G S SL).denote x).property

def embedding : macroField S →ₐ[ℚ] O.originalField G :=
  IntermediateField.inclusion (field_le G S SL he hn)

theorem embedding_value (x : macroField S) :
    (embedding G S SL he hn x : AlgebraicComplex)=x :=
  IntermediateField.coe_inclusion (field_le G S SL he hn) x

include he hn in
theorem lifted_source_ambient (q : Input 1 1 (fun _ => n)) :
    ((A.sourceValue (presentation G) (lift G S SL) q : O.originalField G) : AlgebraicComplex)=
      (q.val.realize q.property (macroFamily S) (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  rw [A.sourceValue,ExactSignatureTables.evaluate_eq_decoded]
  simp only [A.sourceTables,LinearEquiv.apply_symm_apply]
  change (O.originalField G).subtype _=_
  rw [←Network.denote_map (O.originalField G).subtype]
  apply congrArg (fun N : Network AlgebraicComplex 0 => N.denote Fin.elim0)
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact denote_lift G S SL he hn x
  · funext e u v
    cases u <;> cases v <;> rfl

include he hn in
theorem lifted_source_value (q : Input 1 1 (fun _ => n)) :
    A.sourceValue (presentation G) (lift G S SL) q=
      embedding G S SL he hn (macroValue S q) := by
  apply Subtype.ext
  rw [lifted_source_ambient G S SL he hn,embedding_value,O.target_exact]

def query := A.query (lift G S SL) (labels G S SL)
def answer := (embedding G S SL he hn).toLinearMap.leftInverse

def answerComputes : Computes (presentation G).encoding (macroPresentation S).encoding
    (answer G S SL he hn) :=
  Holant.LocalDrafts.MainChain.FieldCodec.retractComputes
    (macroPresentation S) (presentation G) (embedding G S SL he hn)

theorem original_tables : A.tables (presentation G) (original G)=O.originalTables G := rfl

include he hn in
theorem query_value (q : Input 1 1 (fun _ => n)) :
    O.originalValue G (query G S SL q)=embedding G S SL he hn (macroValue S q) := by
  exact (A.query_value (presentation G) (original G) (lift G S SL) (labels G S SL)
    (exact G S SL) (native G S SL) q).trans (lifted_source_value G S SL he hn q)

/-- The complete one-query machine uses only original labels, with no directed
pin anywhere in the target dictionary. -/
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 1 1 (fun _ => n)) (macroPresentation S).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (presentation G).encoding
    (macroValue S) (O.originalValue G) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (A.queryComputes (lift G S SL) (labels G S SL))
    (answerComputes G S SL he hn) ((O.originalTables G).outputBound (presentation G))
    (macroValue S) (fun q => by
      change macroValue S q=answer G S SL he hn (O.originalValue G (query G S SL q))
      rw [query_value G S SL he hn]
      exact (Holant.LocalDrafts.MainChain.FieldCodec.retract_embedding (embedding G S SL he hn) _).symm)

theorem query_counts (q : Input 1 1 (fun _ => n)) :
    (query G S SL q).val.vertices.length=q.val.vertices.length*S.shape.vertices ∧
    (query G S SL q).val.edges.length=q.val.edges.length+q.val.vertices.length*S.shape.edges :=
  A.query_counts (lift G S SL) (labels G S SL) q

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningFieldBridge
