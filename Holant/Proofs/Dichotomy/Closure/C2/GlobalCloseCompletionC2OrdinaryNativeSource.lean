import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorCodec
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2NativePairOutcome
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinFiniteEq4

/-! Generic whole ordinary dictionary to its inverse-source-K native table,
with the exact two coefficient fields and rational answer conversion. Actual
ordinary macro graphs are rebuilt in that native table's own field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryNativeSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue target_exact)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))

def mapped (i : Fin r) : Signature AlgebraicComplex (b i.val) := RingHomRealization.mapSignature K.subtype (H i)
abbrev native := KSourceTransport.nativeSignatures (mapped K H)
abbrev tables := QuaternaryOrdinaryCompanion.tables F H
abbrev value := (tables K F H).evaluate F
abbrev field := O.originalField (native K H)
local instance : Algebra ℚ (field K H) := (field K H).algebra'
abbrev presentation := O.originalPresentation (native K H)
abbrev nativeValue := O.originalValue (native K H)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding r 1 b

def table (i : Fin r) : Signature (field K H) (b i.val) :=
  fun x=>fieldCoefficient (O.coefficients (native K H)) ⟨i,x⟩

theorem table_value (i : Fin r) (x : Fin (b i.val)→Bool) :
    (table K H i x : AlgebraicComplex)=native K H i x := rfl

theorem tables_exact : GeneralEOPinnedDescentAccess.tables (presentation K H) (table K H)=
    O.originalTables (native K H) := rfl

theorem mapped_value (q : ExactSignatureTables.Input r 1 b) :
    K.val.toRingHom (value K F H q)=
      (q.val.realize q.property (mapped K H) KSourceTransport.equalityEdges).denote Fin.elim0 := by
  change K.val.toRingHom ((tables K F H).evaluate F q)=_
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  rw [←Network.denote_map K.val.toRingHom]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  funext e x y
  cases x <;> cases y <;> simp [KSourceTransport.equalityEdges,Signature.equality]

theorem native_value (q : ExactSignatureTables.Input r 1 b) :
    (nativeValue K H q : AlgebraicComplex)=K.val.toRingHom (value K F H q) := by
  have h := KSourceTransport.value_exact (mapped K H) q
  rw [OriginalFamily.value_exact,OriginalFamily.value_exact] at h
  exact (O.target_exact (native K H) q).trans (h.trans (mapped_value K F H q).symm)

def recover : K→ₗ[ℚ] field K H := (field K H).val.toLinearMap.leftInverse.comp K.val.toLinearMap

def recoverComputes : Computes F.encoding (presentation K H).encoding (recover K H) :=
  FieldCodec.computes F (presentation K H) (recover K H)

theorem recover_value (q : ExactSignatureTables.Input r 1 b) :
    nativeValue K H q=recover K H (value K F H q) := by
  change nativeValue K H q=(field K H).val.toLinearMap.leftInverse (K.val.toRingHom (value K F H q))
  rw [←native_value K F H q]
  exact (FieldCodec.retract_embedding (field K H).val (nativeValue K H q)).symm

def source : LengthControlledOracleReduction (inputEncoding (r:=r) (b:=b)) (presentation K H).encoding
    (inputEncoding (r:=r) (b:=b)) F.encoding
    (GeneralEOPinnedDescentAccess.targetValue (presentation K H) (table K H)) (value K F H) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding (r:=r) (b:=b))) (recoverComputes K F H)
    ((tables K F H).outputBound F) (nativeValue K H) (recover_value K F H)

private theorem exact_cast {L : Type} {m n : ℕ} (f : Signature L m) (g : Signature L n)
    (h : (⟨m,f⟩ : AnySignature L)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

def graph {n : ℕ} (N : Macro H n) : Network (field K H) n :=
  N.labels.sourceNetwork (table K H) (fun _ : Fin 1=>Signature.disequality)

def ambientGraph {n : ℕ} (N : Macro H n) : Network AlgebraicComplex n :=
  OpenHolographic.transform (N.network.map K.subtype) sourceKBasis.matrix sourceKBasis.inverse

theorem map_graph {n : ℕ} (N : Macro H n) :
    (graph K H N).map (field K H).subtype=ambientGraph K H N := by
  unfold Network.map graph Labelling.sourceNetwork ambientGraph OpenHolographic.transform
  congr 1
  · funext v x
    change sourceKBasis.symm.action (mapped K H (N.labels.vertex v))
      (fun i=>x (Fin.cast (N.labels.vertex_arity v) i))=
        sourceKBasis.symm.action (RingHomRealization.mapSignature K.subtype (N.network.vertex v)) x
    exact exact_cast _ _
      (congrArg (fun f : AnySignature AlgebraicComplex=>
        (⟨f.1,sourceKBasis.symm.action f.2⟩ : AnySignature AlgebraicComplex))
        (congrArg (RingHomRealization.mapAny K.subtype) (N.exact v))) (N.labels.vertex_arity v) x
  · funext e x y
    change (field K H).subtype (Signature.disequality x y)=
      Kernel.pullback (fun u v=>K.subtype (N.network.edge e u v)) sourceKBasis.matrix x y
    rw [N.edges]
    have equality : (fun u v=>K.subtype (Signature.equality u v))=(Signature.equality : Kernel AlgebraicComplex) := by
      funext u v
      cases u <;> cases v <;> rfl
    rw [equality,sourceKBasis_pullback]
    cases x <;> cases y <;> rfl

theorem graph_value {n : ℕ} (N : Macro H n) (x : Fin n→Bool) :
    ((graph K H N).denote x : AlgebraicComplex)=
      sourceKBasis.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote) x := by
  change (field K H).subtype ((graph K H N).denote x)=_
  rw [←Network.denote_map (field K H).subtype,map_graph,ambientGraph,
    OpenHolographic.denote_transform _ _ _ sourceKBasis.matrix_inverse]
  change sourceKBasis.symm.action ((N.network.map K.subtype).denote) x=_
  congr 1
  funext y
  exact Network.denote_map K.subtype N.network y

def graphMacro (N : Macro H 4) : GlobalCloseCompletionC2NativePairOutcome.Macro (table K H) where
  network := graph K H N
  labels := N.labels
  exact := by
    intro v
    apply Sigma.ext (N.labels.vertex_arity v)
    exact HEq.symm (EdgeSubdivision.signature_cast_heq (N.labels.vertex_arity v) (table K H (N.labels.vertex v)))
  native := fun _=>rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryNativeSource
end
