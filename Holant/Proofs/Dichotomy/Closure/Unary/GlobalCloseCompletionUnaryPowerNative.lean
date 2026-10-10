import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryNativeSource
import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.SourceCodec

/-! A genuine ordinary unary power becomes the exact native power macro
required by the implemented residue-grouping extractor. The normalized K
transport has no discarded edge or vertex scalar. This permits extraction
of a repeated unary factor without a common-one-sided hypothesis: the actual
power graph, rather than an inferred factor gadget, is the source resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPowerNative
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open BinaryCompose Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
namespace S
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.SourceCodec
  (signatures field presentation encoding value controlled)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val))

def native : (i : Fin r)→Signature AlgebraicComplex (b i.val) := KSourceTransport.nativeSignatures H
def vector (u : Bool→AlgebraicComplex) : Bool→AlgebraicComplex :=
  fun a=>∑v : Bool,sourceKBasis.inverse a v*u v

theorem action_power (u : Bool→AlgebraicComplex) (c : AlgebraicComplex) (n : ℕ) :
    sourceKBasis.symm.action (fun x=>c*Signature.unaryPower u n x)=
      fun x=>c*Signature.unaryPower (vector u) n x := by
  classical
  funext x
  simp only [InvertibleKernel.action,InvertibleKernel.symm,Signature.coordinateAction,Signature.unaryPower,vector]
  rw [Fintype.prod_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib]
  ring

variable {n : ℕ} (N : Network AlgebraicComplex n) (NL : Labelling N.shape r 1 b)
variable (exactN : LabelledNetwork.Exact H N NL) (ordinaryN : ∀e,N.edge e=Signature.equality)

def graph : Network AlgebraicComplex n :=
  OpenHolographic.transform N sourceKBasis.matrix sourceKBasis.inverse

def labels : Labelling (graph N).shape r 1 b := NL

include exactN in
theorem exact : LabelledNetwork.Exact (native H) (graph N) (labels N NL) := by
  intro v
  exact congrArg (fun f : AnySignature AlgebraicComplex=>
    (⟨f.1,sourceKBasis.symm.action f.2⟩ : AnySignature AlgebraicComplex)) (exactN v)

include ordinaryN in
theorem edges : ∀e,(graph N).edge e=Signature.disequality := by
  intro e
  change Kernel.pullback (N.edge e) sourceKBasis.matrix=Signature.disequality
  rw [ordinaryN e,sourceKBasis_pullback]

theorem denote : (graph N).denote=sourceKBasis.symm.action N.denote :=
  OpenHolographic.denote_transform N sourceKBasis.matrix sourceKBasis.inverse sourceKBasis.matrix_inverse

private theorem exact_cast {m n : ℕ} (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (h : (⟨m,f⟩ : AnySignature AlgebraicComplex)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h;rfl

include exactN ordinaryN in
theorem template_denote : ((labels N NL).template.network (labels N NL).wellFormed
    (native H) (fun _=>Signature.disequality)).denote=(graph N).denote := by
  rw [Labelling.denote_template]
  apply Network.denote_congr
  · intro v x
    exact exact_cast _ _ (exact H N NL exactN v) ((labels N NL).vertex_arity v) x
  · intro e a b
    exact congrFun (congrFun (edges N ordinaryN e).symm a) b

variable (positive : 0<n) (u : Bool→AlgebraicComplex) (c : AlgebraicComplex) (nonzero : c≠0)
variable (form : N.denote=fun x=>c*Signature.unaryPower u n x)

def power : PowerMacro (native H) (vector u) where
  exponent := n
  positive := positive
  scale := c
  scale_ne_zero := nonzero
  network := graph N
  labels := labels N NL
  value := by
    rw [template_denote H N NL exactN ordinaryN,denote,form,action_power]

/-- Both extractor slots use the same real power macro. Its residue classes
and zero classes are handled inside the checked grouping machine. -/
def nativeSource := S.controlled (native H) (vector u) (vector u)
  (power H N NL exactN ordinaryN positive u c nonzero form)
  (power H N NL exactN ordinaryN positive u c nonzero form)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPowerNative
end
