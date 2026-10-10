import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPinsX
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiComplete

/-! A genuine ordinary q4 with two live mixed coefficients yields an actual
full weighted antidiagonal over its Eq4/pin source's own field. The real graph
adjoin and complete weighted-anti theorem preserve every old source row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPinAntiLift
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
  c : AlgebraicComplex
  d : AlgebraicComplex
  cNonzero : c≠0
  dNonzero : d≠0
  pinned : ∀x : Fin 2→Bool,network.denote ![false,true,x 0,x 1]=NoXWeightedAntiSigned.anti c d x

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

def pins (p : Bool) : Macro src.H 1 := Macro.row (src.p p) (QuaternaryUnaryAccess.pin p) (src.hp p)

theorem cap_word {L : Type} [Field L] {r : ℕ} {b : ℕ→ℕ}
    {H : (i : Fin r)→Signature L (b i.val)} (N : Macro H 4) (p : Bool→Macro H 1)
    (hp : ∀t,(p t).network.denote=QuaternaryUnaryAccess.pin t) :
    (GlobalCloseCompletionC2OrdinaryPinsX.cap N p 1).network.denote=
      fun x=>N.network.denote ![false,true,x 0,x 1] := by
  funext x
  simp [GlobalCloseCompletionC2OrdinaryPinsX.cap,GlobalCloseCompletionC2OrdinaryPinsX.pinOrder,
    Macro.contract_denote,Macro.reindex_denote,Macro.tensor_denote,
    Signature.tensor_apply,Tensor.reindex,hp,QuaternaryUnaryAccess.pin]
  apply congrArg N.network.denote
  funext i
  fin_cases i <;> rfl

def antiMacro : Macro src.H 2 :=
  GlobalCloseCompletionC2OrdinaryPinsX.cap (liftedMacro G src D) (pins G src) 1

theorem mapped_anti (x : Fin 2→Bool) :
    src.K.subtype ((antiMacro G src D).network.denote x)=NoXWeightedAntiSigned.anti D.c D.d x := by
  have h := congrFun (cap_word (liftedMacro G src D) (pins G src)
    (fun p=>Macro.row_denote (src.p p) _ (src.hp p))) x
  change src.K.subtype ((GlobalCloseCompletionC2OrdinaryPinsX.cap (liftedMacro G src D) (pins G src) 1).network.denote x)=_
  rw [h]
  exact (lifted_value G src D _).trans (D.pinned x)

def left : src.K := (antiMacro G src D).network.denote ![false,true]
def right : src.K := (antiMacro G src D).network.denote ![true,false]

theorem left_value : (left G src D : AlgebraicComplex)=D.c := mapped_anti G src D ![false,true]
theorem right_value : (right G src D : AlgebraicComplex)=D.d := mapped_anti G src D ![true,false]

theorem anti_denote : (antiMacro G src D).network.denote=NoXWeightedAntiSigned.anti (left G src D) (right G src D) := by
  funext x
  apply src.K.subtype.injective
  apply (mapped_anti G src D x).trans
  cases h0 : x 0 <;> cases h1 : x 1
  all_goals simp only [NoXWeightedAntiSigned.anti,h0,h1,Bool.false_eq_true,Bool.true_eq_false,
    if_false,if_true,map_zero]
  · exact (left_value G src D).symm
  · exact (right_value G src D).symm

theorem left_nonzero : left G src D≠0 := by
  intro zero
  apply D.cNonzero
  rw [←left_value,zero]
  rfl

theorem right_nonzero : right G src D≠0 := by
  intro zero
  apply D.dNonzero
  rw [←right_value,zero]
  rfl

def output : NoXOrdinaryGraphAdjoin.Output src.H 2 where
  network := (antiMacro G src D).network
  labels := (antiMacro G src D).labels
  exact := (antiMacro G src D).exact
  ordinary := (antiMacro G src D).edges

def data : GenericOrdinarySource.Data G := NoXOrdinaryGraphSource.data G src (output G src D)

theorem old_included : GenericOrdinarySource.family G src⊆GenericOrdinarySource.family G (data G src D) :=
  NoXOrdinaryGraphSource.old_included G src (output G src D)

include D in
theorem classified : Tract (GenericOrdinarySource.family G src) ∨
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
      (OriginalForestSource.value G) := by
  have literal : (⟨(data G src D).b (NoXOrdinaryGraphAdjoin.newLabel src.H).val,
      (data G src D).H (NoXOrdinaryGraphAdjoin.newLabel src.H)⟩ : AnySignature src.K)=
      ⟨2,NoXWeightedAntiSigned.anti (left G src D) (right G src D)⟩ :=
    (NoXOrdinaryGraphSource.new_literal G src (output G src D)).trans
      (congrArg (fun f : Signature src.K 2=>(⟨2,f⟩ : AnySignature src.K)) (anti_denote G src D))
  rcases NoXWeightedAntiComplete.tract_or_hard G (data G src D)
    (NoXOrdinaryGraphAdjoin.newLabel src.H) (left G src D) (right G src D)
    (left_nonzero G src D) (right_nonzero G src D)
    literal with tract|hard
  · exact Or.inl (tract.mono_family (old_included G src D))
  · exact Or.inr hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPinAntiLift
end
