import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOrdinaryEquality
import Holant.Proofs.Hardness.GeneralOddNonisotropicFrame
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra

/-! The actual ordinary nonisotropic-unary chart has an implemented source
programme before any equality anchor is known. Ordered raw graphs are kept;
the norm inverse is charged once per edge by the fixed-field power machine.
No frame or its inverse is installed as a physical vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryChartSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace U
export GeneralOddNonisotropicFrame (frame norm chart inverse inverse_frame)
end U
namespace Q
export GlobalCloseCompletionUnaryOrdinaryEquality (endpoint)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {n s : ℕ} {a : ℕ→ℕ}

def scale (u : Signature K 1) : K := (U.norm u)⁻¹

theorem pulled_edge (u : Signature K 1) (hu : U.norm u≠0) :
    Kernel.pullback Signature.equality (U.inverse u)=fun b c=>scale u*Signature.equality b c := by
  funext b c
  cases b <;> cases c <;>
    simp [Kernel.pullback,Kernel.mul,Kernel.transpose,U.inverse,U.frame,Signature.equality,scale]
  all_goals field_simp [hu]
  all_goals simp only [U.norm] <;> ring

def chartTable (H : (i : Fin s)→Signature K (a i.val)) (u : Signature K 1)
    (i : Fin s) : Signature K (a i.val) := U.chart u (H i)

def graph (u : Signature K 1) (N : Network K n) : Network K n where
  shape := N.shape
  vertex v := U.chart u (N.vertex v)
  edge _ := Signature.equality

theorem graph_value (u : Signature K 1) (hu : U.norm u≠0) (N : Network K n)
    (hN : ∀e,N.edge e=Signature.equality) :
    U.chart u N.denote=fun x=>scale u^N.shape.edges*(graph u N).denote x := by
  have eqn : OpenHolographic.transform N (U.inverse u) (U.frame u)=
      (graph u N).scaleEdges (fun _=>scale u) := by
    unfold OpenHolographic.transform graph Network.scaleEdges
    congr 1
    funext e
    rw [hN e,pulled_edge u hu]
  change Signature.coordinateAction (fun _=>U.frame u) N.denote=_
  rw [←OpenHolographic.denote_transform N (U.inverse u) (U.frame u) (U.inverse_frame u hu),eqn]
  funext x
  rw [Network.denote_scaleEdges]
  simp [graph]

def labels (u : Signature K 1) (N : Network K n) (NL : Labelling N.shape s 1 a) :
    Labelling (graph u N).shape s 1 a := NL

theorem exact (H : (i : Fin s)→Signature K (a i.val)) (u : Signature K 1)
    (N : Network K n) (NL : Labelling N.shape s 1 a) (hN : LabelledNetwork.Exact H N NL) :
    LabelledNetwork.Exact (chartTable H u) (graph u N) (labels u N NL) := by
  intro v
  exact congrArg (fun f : AnySignature K=>(⟨f.1,U.chart u f.2⟩ : AnySignature K)) (hN v)

theorem graph_endpoint (u : Signature K 1) (hu : U.norm u≠0) (N : Network K n)
    (hO : ∀e,N.edge e=Signature.equality) (A B : K)
    (hN : U.chart u N.denote=Q.endpoint n A B) :
    (graph u N).denote=Q.endpoint n (U.norm u^N.shape.edges*A) (U.norm u^N.shape.edges*B) := by
  have h := graph_value u hu N hO
  rw [hN] at h
  funext x
  have hv := congrFun h x
  have value : (graph u N).denote x=U.norm u^N.shape.edges*Q.endpoint n A B x := by
    rw [hv]
    change (graph u N).denote x=U.norm u^N.shape.edges*((U.norm u)⁻¹^N.shape.edges*(graph u N).denote x)
    rw [←mul_assoc,←mul_pow,mul_inv_cancel₀ hu,one_pow,one_mul]
  rw [value]
  simp only [Q.endpoint,Pi.add_apply,Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.purePin]
  split_ifs <;> ring

section Source
variable [Algebra ℚ K] {degree : ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))
variable (u : Signature K 1) (hu : U.norm u≠0)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev oldTables := QuaternaryOrdinaryCompanion.tables F H
abbrev tables := QuaternaryOrdinaryCompanion.tables F (chartTable H u)
abbrev transformed := HolographicTransport.tables F (oldTables F H) (U.inverse u) (U.frame u)

theorem transformed_vertex (i : Fin s) (x : Fin (a i.val)→Bool) :
    F.decode ((transformed F H u).vertex i x)=chartTable H u i x := by
  simp [transformed,HolographicTransport.tables,oldTables,QuaternaryOrdinaryCompanion.tables,
    chartTable,U.chart]

include hu in
theorem transformed_edge (i : Fin 1) (b c : Bool) :
    F.decode ((transformed F H u).edge i b c)=scale u*Signature.equality b c := by
  simp only [transformed,HolographicTransport.tables,oldTables,QuaternaryOrdinaryCompanion.tables,
    LinearEquiv.apply_symm_apply]
  exact congrFun₂ (pulled_edge u hu) b c

include hu in
/-- One norm inverse occurs for every actual input edge, including loops. -/
theorem transformed_value (r : ExactSignatureTables.Input s 1 a) :
    (transformed F H u).evaluate F r=scale u^r.val.edges.length*(tables F H u).evaluate F r := by
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [Network.denote,RawClosedNetwork.realize]
  simp_rw [transformed_vertex F H u,transformed_edge F H u hu]
  simp only [tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change (∑z,_) = scale u^r.val.edges.length*∑z,_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [RawClosedNetwork.shape]
  ring

def edgeControlled : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a)) F.encoding
    (inputEncoding (s:=s) (a:=a)) F.encoding ((tables F H u).evaluate F) ((transformed F H u).evaluate F) :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq
    (pairComputes (identityComputes (inputEncoding (s:=s) (a:=a))) (Compiler.edgeCountComputes s 1 a))
    (ScalarPower.correction F (scale u)) ((transformed F H u).outputBound F) ((tables F H u).evaluate F)
    (fun r=>by
      change (tables F H u).evaluate F r=_*(scale u)⁻¹^r.val.edges.length
      dsimp only [id,Prod.fst,Prod.snd]
      rw [transformed_value F H u hu]
      exact (ScalarPower.cancel_scale_power (scale u) _ (show scale u≠0 from inv_ne_zero hu) _).symm)

def controlled : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a)) F.encoding
    (inputEncoding (s:=s) (a:=a)) F.encoding ((tables F H u).evaluate F) ((oldTables F H).evaluate F) :=
  Programme.compose (edgeControlled F H u hu)
    (HolographicTransport.fromTransformed F (oldTables F H) (U.inverse u) (U.frame u) (U.inverse_frame u hu))


end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryChartSource
end
