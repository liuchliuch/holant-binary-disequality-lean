import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeFamily
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryEndpointSource
import Holant.Proofs.Hardness.GeneralOddNonisotropicSource
import Holant.Tractable.Conformal

/-! A genuine ordinary nonisotropic unary and failure of the whole-family
criterion produce the endpoint graph internally over the old field. The
higher two-sided arm receives the implemented Eq4/two-pin source. Small
arity and a zero own-axis endpoint remain genuine, explicitly recorded
alternatives; neither is silently turned into a terminal classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryDescentSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
namespace U
export GeneralOddNonisotropicFrame (frame norm chart Ordinary)
export GeneralOddNonisotropicDescent (EndpointSupport descend)
end U
namespace E
export GlobalCloseCompletionUnaryEndpointSource (data chartedFamily charted_included)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (H : (i : Fin r)→Signature L (b i.val))


theorem norm_map (u : Signature L 1) :
    ((U.norm u : L) : AlgebraicComplex)=U.norm (fun x=>(u x : AlgebraicComplex)) := by
  change L.val.toRingHom (U.norm u)=_
  simp [U.norm]

theorem chart_map {n : ℕ} (u : Signature L 1) (f : Signature L n) (x : Fin n→Bool) :
    ((U.chart u f x : L) : AlgebraicComplex)=
      U.chart (fun z=>(u z : AlgebraicComplex)) (fun z=>(f z : AlgebraicComplex)) x := by
  change L.val.toRingHom (U.chart u f x)=_
  simp only [U.chart,Signature.coordinateAction,map_sum,map_mul,map_prod]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases y i <;> simp [U.frame]

def frameBasis (u : Signature AlgebraicComplex 1) (hu : U.norm u≠0) : InvertibleKernel :=
  ⟨U.frame u,GeneralOddNonisotropicFrame.inverse u,
    GeneralOddNonisotropicFrame.frame_inverse u hu,GeneralOddNonisotropicFrame.inverse_frame u hu⟩

theorem frame_conformal (u : Signature AlgebraicComplex 1) :
    Kernel.pullback Signature.equality (U.frame u)=fun p q=>U.norm u*Signature.equality p q := by
  funext p q
  cases p <;> cases q <;>
    simp [Kernel.pullback,Kernel.mul,Kernel.transpose,U.frame,U.norm,Signature.equality]
  all_goals ring

/-- The one actual unary frame transports all seven whole-family clauses.
Its nonunit norm multiplier is kept in the conformal identity. -/
theorem tract_frame (u : Signature AlgebraicComplex 1) (hu : U.norm u≠0)
    (S : SignatureFamily AlgebraicComplex) :
    Tract S ↔ Tract (familyAction (frameBasis u hu) S) := by
  let D := sourceKBasis.symm.comp ((frameBasis u hu).comp sourceKBasis)
  have hK : Kernel.pullback Signature.disequality sourceKBasis.inverse=Signature.equality := by
    rw [←sourceKBasis_pullback,←pullback_mul,sourceKBasis.matrix_inverse]
    simp [Kernel.pullback]
  have hD : XConformal D := by
    refine ⟨U.norm u,hu,?_⟩
    change Kernel.pullback Signature.disequality
      (Kernel.mul sourceKBasis.inverse (Kernel.mul (U.frame u) sourceKBasis.matrix))=_
    rw [pullback_mul,hK,pullback_mul,frame_conformal,Conformal.pullback_scale,sourceKBasis_pullback]
  simpa only [D,Conformal.familyAction_comp,Conformal.familyAction_action_symm,
    Conformal.familyAction_symm_action] using
    xConformal_tract_iff hD (familyAction sourceKBasis.symm S)

theorem charted_exact (u : Signature L 1) (hu : U.norm u≠0) :
    E.chartedFamily L H u=familyAction
      (frameBasis (fun x=>(u x : AlgebraicComplex))
        (by rw [←norm_map]; exact (map_ne_zero L.val.toRingHom).mpr hu)) (ambient L H) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨⟨b i.val,mapped L H i⟩,⟨i,rfl⟩,?_⟩
    apply congrArg (fun g : Signature AlgebraicComplex (b i.val)=>(⟨b i.val,g⟩ : AnySignature AlgebraicComplex))
    funext x
    exact (chart_map L u (H i) x).symm
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩
    refine ⟨i,?_⟩
    apply congrArg (fun g : Signature AlgebraicComplex (b i.val)=>(⟨b i.val,g⟩ : AnySignature AlgebraicComplex))
    funext x
    exact chart_map L u (H i) x

theorem charted_negative (u : Signature L 1) (hu : U.norm u≠0)
    (negative : ¬Tract (ambient L H)) : ¬Tract (E.chartedFamily L H u) := by
  rw [charted_exact L H u hu]
  exact fun h=>negative ((tract_frame _ _ _).mpr h)

theorem off_axis (u : Signature L 1) (hu : U.norm u≠0) (negative : ¬Tract (ambient L H)) :
    ∃j : Fin r,∃x : Fin (b j.val)→Bool,U.chart u (H j) x≠0 ∧ x≠(fun _=>false) := by
  have hnorm : U.norm (fun x=>(u x : AlgebraicComplex))≠0 := by
    rw [←norm_map]
    exact (map_ne_zero L.val.toRingHom).mpr hu
  obtain ⟨j,x,hx,hx0⟩ := GeneralOddNonisotropicSource.off_axis (mapped L H)
    (fun z=>(u z : AlgebraicComplex)) hnorm negative
  refine ⟨j,x,?_,hx0⟩
  intro zero
  apply hx
  change U.chart (fun z=>(u z : AlgebraicComplex)) (fun z=>(H j z : AlgebraicComplex)) x=0
  rw [←chart_map,zero]
  exact map_zero L.val.toRingHom

variable (N : Network L 1) (NL : Labelling N.shape r 1 b)
variable (hE : LabelledNetwork.Exact H N NL) (hO : U.Ordinary N)

/-- The original row, number of actual unary caps and every graph resource
are selected by the genuine cap descent, before any endpoint test. -/
structure Endpoint where
  label : Fin r
  arity : ℕ
  caps : ℕ
  positive : 0<arity
  conservation : arity+caps=b label.val
  graph : Network L arity
  labels : Labelling graph.shape r 1 b
  exact : LabelledNetwork.Exact H graph labels
  ordinary : U.Ordinary graph
  support : U.EndpointSupport (U.chart N.denote graph.denote)
  opposite : U.chart N.denote graph.denote (fun _=>true)≠0
  vertices : graph.shape.vertices=caps*N.shape.vertices+1
  edges : graph.shape.edges=caps*(N.shape.edges+1)

variable (hu : U.norm N.denote≠0) (negative : ¬Tract (ambient L H))

include hE hO hu negative in
theorem endpoint_exists : Nonempty (Endpoint L H N) := by
  obtain ⟨j,x,hx,hx0⟩ := off_axis L H N.denote hu negative
  have uses : Uses N (family L H) := fun v=>⟨NL.vertex v,hE v⟩
  obtain ⟨m,k,hm,hkn,V,hVF,hVE,hVs,hVt,hVv,hVe⟩ :=
    U.descend (family L H) N uses hO (b j.val) (Network.corolla (H j))
      (fun _=>⟨j,rfl⟩) (fun e=>Fin.elim0 e) x (by simpa using hx) hx0
  let labels : Labelling V.shape r 1 b := {
    vertex v := Classical.choose (hVF v)
    vertex_arity v := congrArg Sigma.fst (Classical.choose_spec (hVF v))
    edge _ := 0 }
  refine ⟨⟨j,m,k,hm,hkn,V,labels,(fun v=>Classical.choose_spec (hVF v)),hVE,hVs,hVt,?_,?_⟩⟩
  · simpa [Network.corolla] using hVv
  · simpa [Network.corolla] using hVe

def endpoint : Endpoint L H N := Classical.choice (endpoint_exists L H N NL hE hO hu negative)

section Source
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (F : FixedField L degree)
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))

structure SourceReceipt : Type 1 where
  source : GenericOrdinarySource.Data G
  included : E.chartedFamily L H N.denote⊆GenericOrdinarySource.family G source

theorem SourceReceipt.obstruction (R : SourceReceipt L H N G)
    (hu : U.norm N.denote≠0) (negative : ¬Tract (ambient L H)) :
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G R.source)) := by
  apply (GenericOrdinarySource.rejected_iff G R.source).mp
  exact fun tract=>charted_negative L H N.denote hu negative (tract.mono_family R.included)

/-- No endpoint graph, finite-order period, diagonal inverse or Eq4 anchor
is requested from the caller: the actual higher endpoint is consumed. -/
def higher (D : Endpoint L H N) (large : 3≤D.arity)
    (own : U.chart N.denote D.graph.denote (fun _=>false)≠0) : SourceReceipt L H N G := by
  rcases D with ⟨j,m,k,hm,hkn,V,VL,exactV,ordinary,support,opposite,vertices,edges⟩
  cases m with
  | zero=>exact False.elim (by dsimp at large; omega)
  | succ m=>
    cases m with
    | zero=>exact False.elim (by dsimp at large; omega)
    | succ t=>
      have ht : 0<t := by dsimp at large; omega
      let A := U.chart N.denote V.denote (fun _=>false)
      let B := U.chart N.denote V.denote (fun _=>true)
      have value := GlobalCloseCompletionUnaryHigherEq4.endpoint_of_support
        (U.chart N.denote V.denote) support
      exact ⟨E.data G L F H back N.denote hu V VL exactV ordinary ht A B own opposite value,
        E.charted_included G L F H back N.denote hu V VL exactV ordinary ht A B own opposite value⟩

inductive Outcome (D : Endpoint L H N) : Type 1 where
  | small (arity : D.arity≤2)
  | zero (large : 3≤D.arity) (own : U.chart N.denote D.graph.denote (fun _=>false)=0)
  | sourced (large : 3≤D.arity) (own : U.chart N.denote D.graph.denote (fun _=>false)≠0)
      (receipt : SourceReceipt L H N G)
      (obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction
        (preprocess (GenericOrdinarySource.family G receipt.source)))

/-- The endpoint and its real residual branch are both chosen internally. -/
def complete : Outcome L H N G (endpoint L H N NL hE hO hu negative) := by
  classical
  let D := endpoint L H N NL hE hO hu negative
  by_cases small : D.arity≤2
  · exact .small small
  have large : 3≤D.arity := by omega
  by_cases own : U.chart N.denote D.graph.denote (fun _=>false)=0
  · exact .zero large own
  · let R := higher L H N hu G F back D large own
    exact .sourced large own R (SourceReceipt.obstruction L H N G R hu negative)


end Source

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryDescentSource
end
