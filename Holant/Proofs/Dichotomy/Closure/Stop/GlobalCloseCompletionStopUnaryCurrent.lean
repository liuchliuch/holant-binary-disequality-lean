import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopOrdinarySource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicLift
import Holant.Proofs.Closure.GeneratedGroupWorklistExecution
import Holant.Proofs.Closure.InitialPalette

/-! Consume the SAME retained unary stop in the actual ordinary current
table, without an assumed equality anchor. Positive whole-family instances
receive the original evaluator. A nonisotropic negative instance enters the
internally constructed cap descent and source; the real isotropic and endpoint
residuals stay explicit. No stopped history or retained row is discarded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopUnaryCurrent
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open BinaryCompose
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace O
export GlobalCloseCompletionStopOrdinarySource (field presentation table table_value toOriginal family z_member originalComputes)
end O
namespace D
export GlobalCloseCompletionUnaryDescentSource (ambient endpoint Outcome complete)
end D
namespace U
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame (norm)
end U
namespace I
export GlobalCloseCompletionUnaryIsotropicLift (output independent toOriginal)
end I
namespace L
export GlobalCloseCompletionUnaryLiteralSource (arity signatures)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (O.field G P) := (O.field G P).algebra'
variable (u : Signature (OI.K G) 1) (retained : (⟨1,u⟩ : AnySignature (OI.K G))∈P.family)

def label : Fin P.count := Classical.choose retained
theorem arity : P.arity (label G P u retained).val=1 := congrArg Sigma.fst (Classical.choose_spec retained)
def unary : Signature (O.field G P) 1 :=
  fun x=>O.table G P (label G P u retained) (fun i=>x (Fin.cast (arity G P u retained) i))

private theorem cast_pair {K : Type} {m n : ℕ} (h : m=n) (f : Signature K m) :
    (⟨m,f⟩ : AnySignature K)=⟨n,fun x=>f (fun i=>x (Fin.cast h i))⟩ := by
  cases h
  rfl

theorem literal : (⟨P.arity (label G P u retained).val,O.table G P (label G P u retained)⟩ :
    AnySignature (O.field G P))=⟨1,unary G P u retained⟩ :=
  cast_pair (arity G P u retained) (O.table G P (label G P u retained))

theorem table_nonzero (i : Fin P.count) : O.table G P i≠0 := by
  intro zero
  have hz : sourceKBasis.action (StableHigherCurrentPurePinsCore.mapped G P i)=0 := by
    funext x
    exact (O.table_value G P i x).symm.trans (by
      rw [zero]
      exact map_zero (O.field G P).subtype)
  have hn := (Conformal.action_eq_zero_iff sourceKBasis _).mp hz
  apply P.nonzero i
  funext x
  apply (StableHigherCurrentPurePinsCore.embedding G).injective
  have hx := congrFun hn x
  change (StableHigherCurrentPurePinsCore.embedding G) (P.table i x)=0 at hx
  exact hx.trans (map_zero (StableHigherCurrentPurePinsCore.embedding G)).symm

theorem unary_nonzero : unary G P u retained≠0 := by
  intro zero
  have h := congrArg (fun f : AnySignature (O.field G P)=>f.2=0) (literal G P u retained)
  exact table_nonzero G P (label G P u retained) (h.mpr zero)

def graph : Network (O.field G P) 1 := Network.corolla (unary G P u retained)
def labels : Labelling (graph G P u retained).shape P.count 1 P.arity where
  vertex _ := label G P u retained
  vertex_arity _ := arity G P u retained
  edge e := Fin.elim0 e
theorem exact : LabelledNetwork.Exact (O.table G P) (graph G P u retained) (labels G P u retained) :=
  fun _=>literal G P u retained
theorem ordinary : ∀e,(graph G P u retained).edge e=Signature.equality := fun e=>Fin.elim0 e
theorem graph_nonzero : (graph G P u retained).denote≠0 := by
  rw [graph,Network.denote_corolla]
  exact unary_nonzero G P u retained

theorem ambient_exact : D.ambient (O.field G P) (O.table G P)=O.family G P := rfl

abbrev Descent (hu : U.norm (graph G P u retained).denote≠0) (negative : ¬Tract (O.family G P)) :=
  D.Outcome (O.field G P) (O.table G P) (graph G P u retained) G
    (D.endpoint (O.field G P) (O.table G P) (graph G P u retained) (labels G P u retained)
      (exact G P u retained) (ordinary G P u retained) hu negative)

def descend (hu : U.norm (graph G P u retained).denote≠0) (negative : ¬Tract (O.family G P)) :
    Descent G P u retained hu negative :=
  D.complete (O.field G P) (O.table G P) (graph G P u retained) (labels G P u retained)
    (exact G P u retained) (ordinary G P u retained) hu negative G (O.presentation G P) (O.toOriginal G P)

def isotropicOutput := I.output (O.field G P) (O.table G P) (O.z_member G P)
  (graph G P u retained) (labels G P u retained) (exact G P u retained) (ordinary G P u retained)

theorem isotropic_independent (isotropic : U.norm (graph G P u retained).denote=0) :
    GlobalCloseCompletionUnaryIsotropicSource.determinant (graph G P u retained).denote
      (isotropicOutput G P u retained).network.denote≠0 :=
  I.independent (O.field G P) (O.table G P) (O.z_member G P)
    (graph G P u retained) (labels G P u retained) (exact G P u retained) (ordinary G P u retained)
    (graph_nonzero G P u retained) isotropic

abbrev isoArity := L.arity (O.table G P) (isotropicOutput G P u retained)
abbrev isoTable := L.signatures (O.presentation G P) (O.table G P) (isotropicOutput G P u retained)
abbrev IsotropicAccess := PhysicalProgramme
  (RawClosedNetwork.validatedEncoding (P.count+1) 1 (isoArity G P u retained)) (O.presentation G P).encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables (O.presentation G P) (isoTable G P u retained)).evaluate (O.presentation G P))
  (OriginalForestSource.value G)

def isotropicSource : IsotropicAccess G P u retained :=
  PhysicalProgramme.ofControlled (I.toOriginal (O.field G P) (O.table G P) (O.z_member G P)
    (graph G P u retained) (labels G P u retained) (exact G P u retained) (ordinary G P u retained)
    (O.presentation G P) G (O.toOriginal G P))

inductive Completion : Type 1 where
  | tract (criterion : Tract (O.family G P))
      (evaluator : Computes (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
        (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G))
  | isotropic (negative : ¬Tract (O.family G P)) (norm_zero : U.norm (graph G P u retained).denote=0)
      (independent : GlobalCloseCompletionUnaryIsotropicSource.determinant
        (graph G P u retained).denote (isotropicOutput G P u retained).network.denote≠0)
      (source : IsotropicAccess G P u retained)
  | nonisotropic (negative : ¬Tract (O.family G P)) (norm_nonzero : U.norm (graph G P u retained).denote≠0)
      (descent : Descent G P u retained norm_nonzero negative)

def complete : Completion G P u retained := by
  classical
  by_cases tract : Tract (O.family G P)
  · exact .tract tract (O.originalComputes G P tract)
  by_cases isotropic : U.norm (graph G P u retained).denote=0
  · exact .isotropic tract isotropic (isotropic_independent G P u retained isotropic) (isotropicSource G P u retained)
  · exact .nonisotropic tract isotropic (descend G P u retained isotropic tract)

def ForStop (stop : OccurrenceWorklist.Stop G P) : Type 1 :=
  match stop with
  | .unary u retained _=>Completion G P u retained
  | .infinite ..=>PUnit.{2}
  | .odd ..=>PUnit.{2}
def forStop (stop : OccurrenceWorklist.Stop G P) : ForStop G P stop :=
  match stop with
  | .unary u retained _=>complete G P u retained
  | .infinite ..=>PUnit.unit
  | .odd ..=>PUnit.unit

variable (base : Palette G)
def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop stop _=>ForStop G base stop
  | .prepared _ _ (.inl stopped)=>ForStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _)=>PUnit.{2}
def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop stop _=>forStop G base stop
  | .prepared _ _ (.inl stopped)=>forStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _)=>PUnit.unit

/-- Original G is the sole input. The retained unary, its actual coordinate
field and graph, negative test, endpoint and source are all selected inside. -/
def original_unary_sources : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopUnaryCurrent
end
