import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPinsX
import Holant.Proofs.Dichotomy.General.GenericOrdinaryScalarXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal

/-! A real ordinary q4 graph over an Eq4/pin source yields the literal-X
negative theorem. The same graph is rebuilt in that source's actual field
using its literal row labels; every parameter is recovered from an original
coefficient. No ambient-to-source scalar inverse is presumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryLift
open Computability Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'

structure Input where
  network : Network AlgebraicComplex 4
  uses : ∀v,(⟨network.shape.arity v,network.vertex v⟩ : AnySignature AlgebraicComplex)∈GenericOrdinarySource.family G src
  ordinary : ∀e,network.edge e=Signature.equality
  a : AlgebraicComplex
  b : AlgebraicComplex
  c : AlgebraicComplex
  d : AlgebraicComplex
  aNonzero : a≠0
  cNonzero : c≠0
  dNonzero : d≠0
  form : network.denote=T.normal a b c d

variable (D : Input G src)

def mapped (i : Fin src.size) : Signature AlgebraicComplex (src.b i.val) :=
  RingHomRealization.mapSignature src.K.subtype (src.H i)

def labels := UniversalPairReduction.FiniteFamily.labelling (mapped G src) D.network D.uses

def lifted : Network src.K 4 := (labels G src D).sourceNetwork src.H (fun _ : Fin 1=>Signature.equality)

private theorem exact_cast {L : Type} {m n : ℕ} (f : Signature L m) (g : Signature L n)
    (h : (⟨m,f⟩ : AnySignature L)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem map_lifted : (lifted G src D).map src.K.subtype=D.network := by
  unfold Network.map lifted Labelling.sourceNetwork
  congr 1
  · funext v x
    change mapped G src ((labels G src D).vertex v)
      (fun i=>x (Fin.cast ((labels G src D).vertex_arity v) i))=D.network.vertex v x
    exact exact_cast _ _ (D.uses v).choose_spec ((labels G src D).vertex_arity v) x
  · funext e b c
    change src.K.subtype (Signature.equality b c)=D.network.edge e b c
    rw [D.ordinary]
    cases b <;> cases c <;> rfl

theorem lifted_value (x : Fin 4→Bool) :
    src.K.subtype ((lifted G src D).denote x)=D.network.denote x := by
  rw [←Network.denote_map src.K.subtype,map_lifted]

def liftedMacro : Macro src.H 4 where
  network := lifted G src D
  labels := labels G src D
  exact := by
    intro v
    apply Sigma.ext ((labels G src D).vertex_arity v)
    exact HEq.symm (EdgeSubdivision.signature_cast_heq ((labels G src D).vertex_arity v)
      (src.H ((labels G src D).vertex v)))
  edges := fun _=>rfl

def word : Fin 4→(Fin 4→Bool) :=
  ![![false,false,false,false],![false,false,true,true],![false,true,false,true],![false,true,true,false]]

def coefficient (i : Fin 4) : src.K := (lifted G src D).denote (word i)

theorem coefficient_value (i : Fin 4) :
    (coefficient G src D i : AlgebraicComplex)=(![D.a,D.b,D.c,D.d] : Fin 4→AlgebraicComplex) i := by
  change src.K.subtype ((lifted G src D).denote (word i))=_
  rw [lifted_value,D.form]
  fin_cases i <;> rfl

theorem normal_form : (liftedMacro G src D).network.denote=T.normal
    (coefficient G src D 0) (coefficient G src D 1) (coefficient G src D 2) (coefficient G src D 3) := by
  funext x
  apply src.K.subtype.injective
  change src.K.subtype ((lifted G src D).denote x)=_
  rw [lifted_value,D.form]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]
  all_goals first
    | exact (coefficient_value G src D 0).symm
    | exact (coefficient_value G src D 1).symm
    | exact (coefficient_value G src D 2).symm
    | exact (coefficient_value G src D 3).symm

def pins (p : Bool) : Macro src.H 1 := Macro.row (src.p p) (QuaternaryUnaryAccess.pin p) (src.hp p)

theorem coefficient_nonzero (i : Fin 4) (h : (![D.a,D.b,D.c,D.d] : Fin 4→AlgebraicComplex) i≠0) :
    coefficient G src D i≠0 := by
  intro zero
  apply h
  rw [←coefficient_value,zero]
  rfl

def output : GlobalCloseCompletionOrdinaryXAdjoin.Output src.H :=
  GlobalCloseCompletionC2OrdinaryPinsX.output (liftedMacro G src D) (pins G src)
    (coefficient G src D 0) (coefficient G src D 1) (coefficient G src D 2) (coefficient G src D 3)
    (coefficient_nonzero G src D 0 D.aNonzero)
    (coefficient_nonzero G src D 2 D.cNonzero)
    (coefficient_nonzero G src D 3 D.dNonzero)
    (normal_form G src D) (fun p=>Macro.row_denote (src.p p) _ (src.hp p))

def data : GenericLiteralXSource.Data G := GenericOrdinaryScalarXSource.data G src (output G src D)

theorem old_included : GenericOrdinarySource.family G src⊆GenericLiteralXSource.family G (data G src D) :=
  GenericOrdinaryScalarXSource.old_included G src (output G src D)

include D in
theorem classified : Tract (GenericOrdinarySource.family G src) ∨
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
      (OriginalForestSource.value G) := by
  classical
  by_cases tract : Tract (GenericOrdinarySource.family G src)
  · exact Or.inl tract
  · right
    apply OrdinaryNegativeGenericXUniversal.countingHard G (data G src D)
    apply (GenericLiteralXSource.rejected_iff G (data G src D)).mp
    intro h
    exact tract (h.mono_family (old_included G src D))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryLift
end
