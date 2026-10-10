import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWGraph
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSymmetricDecomposition
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZActual

/-! A genuine symmetric prime ternary and retained Z produce an actual
symmetric GHZ graph over the same dictionary, including the W orbit. Its
implemented whole-family source then has literal equality-three with the
exact Gram edge. This is not identified with an ordinary equality-three
source or an assumed CSP classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSymmetricSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
end C
namespace S
export GlobalCloseCompletionTernaryGHZSymmetry (symmetric values)
end S
namespace Z
export GlobalCloseCompletionUnaryIsotropicSource (z)
end Z
namespace A
export GlobalCloseCompletionSymmetricGHZActual (toOriginal ghz_literal old_included)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {b : ℕ→ℕ}
variable (phi : K→+*AlgebraicComplex) (H : (i : Fin r)→Signature K (b i.val))

structure Output where
  resource : Macro H 3
  basis : InvertibleKernel
  form : RingHomRealization.mapSignature phi resource.network.denote=C.ghz basis.matrix

variable (N : Macro H 3) (D : Macro H 2) (zForm : D.network.denote=Z.z)
variable (symmetric : RingHomRealization.mapSignature phi N.network.denote=
  S.symmetric (S.values (RingHomRealization.mapSignature phi N.network.denote)))
variable (prime : Prime (⟨3,RingHomRealization.mapSignature phi N.network.denote⟩ : AnySignature AlgebraicComplex))

include N D zForm symmetric prime in
theorem exists_output : Nonempty (Output phi H) := by
  rcases GlobalCloseCompletionIndependentPinsSymmetricDecomposition.symmetric_prime
    (RingHomRealization.mapSignature phi N.network.denote) symmetric prime with ghz|w
  · obtain ⟨R,hR⟩:=ghz
    exact ⟨⟨N,R,hR⟩⟩
  · obtain ⟨R,hR⟩:=w
    obtain ⟨v,Q,hQ⟩:=GlobalCloseCompletionIndependentPinsWGraph.produces phi N D zForm R hR
    exact ⟨⟨GlobalCloseCompletionIndependentPinsWGraph.graph N D v,Q,hQ⟩⟩

def produce : Output phi H := Classical.choice (exists_output phi H N D zForm symmetric prime)

def asOutput (out : Output phi H) : NoXOrdinaryGraphAdjoin.Output H 3 :=
  ⟨out.resource.network,out.resource.labels,out.resource.exact,out.resource.edges⟩

theorem asOutput_form (out : Output phi H) :
    RingHomRealization.mapSignature phi (asOutput phi H out).network.denote=C.ghz out.basis.matrix := out.form

attribute [local irreducible] asOutput

section Original
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (T : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F T).evaluate F) (OriginalForestSource.value G))
variable (out : Output L.subtype T)

def toOriginal := A.toOriginal G L F T back (asOutput L.subtype T out) out.basis

abbrev ghz_literal :=
  A.ghz_literal L F T (asOutput L.subtype T out) out.basis (asOutput_form L.subtype T out)

end Original

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSymmetricSource
end
