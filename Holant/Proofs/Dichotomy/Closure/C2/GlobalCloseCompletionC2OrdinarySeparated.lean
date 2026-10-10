import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryTwist
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins

/-! The genuine ordinary-Z separating graph is installed into the complete
old ordinary source table, with exact original-G backtransfer. Eq4 and both
pins are conclusions of the existing anchor programme; no changed-coordinate
table is presented as a native Palette. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinarySeparated
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace T
export GlobalCloseCompletionC2OrdinaryTwist (eq4Graph eq4Graph_denote eq4Labels eq4_exact eq4_ordinary)
end T
namespace N
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end N
namespace Z
export GlobalCloseCompletionKleinOrdinaryPair (zSignature)
end Z
namespace Pn
export GlobalCloseCompletionOrdinaryAnchorPins (data old_included)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))

structure Input : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K := K.algebra'; FixedField K degree
  count : ℕ
  b : ℕ→ℕ
  H : (i : Fin count)→Signature K (b i.val)
  graph : Network K 4
  labels : Labelling graph.shape count 1 b
  exact : LabelledNetwork.Exact H graph labels
  ordinary : ∀e,graph.edge e=Signature.equality
  zLabel : Fin count
  z : K
  zNonzero : z≠0
  zLiteral : (⟨b zLabel.val,H zLabel⟩ : AnySignature K)=⟨2,Z.zSignature z⟩
  a : K
  b0 : K
  c : K
  d : K
  form : graph.denote=N.normal a b0 c d
  separated : (a^2-b0^2)^2≠(c^2-d^2)^2
  toOriginal : letI : Algebra ℚ K := K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G)

variable (D : Input G)
local instance : Algebra ℚ D.K := D.K.algebra'

def coefficient : D.K := D.z^6*((D.a^2-D.b0^2)^2-(D.c^2-D.d^2)^2)

theorem coefficient_nonzero : coefficient G D≠0 :=
  mul_ne_zero (pow_ne_zero _ D.zNonzero) (sub_ne_zero.mpr D.separated)

def anchor : GlobalCloseCompletionOrdinaryAnchorInput.Input G where
  K := D.K
  degree := D.degree
  F := D.F
  count := D.count
  b := D.b
  H := D.H
  graph := T.eq4Graph D.graph D.z
  labels := T.eq4Labels D.H D.graph D.labels D.zLabel D.z D.zLiteral
  exact := T.eq4_exact D.H D.graph D.labels D.zLabel D.z D.zLiteral D.exact
  ordinary := T.eq4_ordinary D.graph D.z D.ordinary
  scalar := coefficient G D
  nonzero := coefficient_nonzero G D
  denote := T.eq4Graph_denote D.graph D.z D.a D.b0 D.c D.d D.form
  toOriginal := D.toOriginal

def data : GenericOrdinarySource.Data G := Pn.data G (anchor G D)

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin D.count=>
  RingHomRealization.mapAny D.K.subtype (⟨D.b i.val,D.H i⟩ : AnySignature D.K)

theorem old_included : family G D⊆GenericOrdinarySource.family G (data G D) :=
  Pn.old_included G (anchor G D)

theorem obstruction (negative : ¬Tract (family G D)) :
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G (data G D))) := by
  apply (GenericOrdinarySource.rejected_iff G (data G D)).mp
  intro tract
  exact negative (tract.mono_family (old_included G D))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinarySeparated
end
