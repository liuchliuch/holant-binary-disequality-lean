import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryTraceSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTraceOrX
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZRows
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSource

/-! The trace-or-X provenance carried by an actual two-pin source survives
to the ternary consumer. Its ambient row is pulled back to a real corolla;
the resulting symmetric GHZ graph uses exactly the same complete table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsResourceTernary
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace U
export GlobalCloseCompletionUnaryDescentSource (ambient)
export GlobalCloseCompletionUnaryTraceOrX (Witness)
end U
namespace R
export GlobalCloseCompletionSymmetricGHZRows (row value)
end R
namespace T
export GlobalCloseCompletionIndependentPinsTernaryTraceSource (produce)
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end T
namespace S
export GlobalCloseCompletionIndependentPinsSymmetricSource (Output)
export GlobalCloseCompletionIndependentPinsSource (Data family)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))

theorem x_form : (xAnchor : Signature AlgebraicComplex 2)=T.binary 0 1 1 := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [xAnchor,kernelSignature,Signature.disequality,T.binary,h0,h1]

theorem exists_output (N : Macro H 3) (prime : Prime (⟨3,N.network.denote⟩ : AnySignature L))
    (resource : U.Witness (U.ambient L H)) : Nonempty (S.Output L.subtype H) := by
  have mapped : Prime (⟨3,RingHomRealization.mapSignature L.subtype N.network.denote⟩ : AnySignature AlgebraicComplex):=
    (prime_mapSignature_iff L.subtype _).mpr prime
  cases resource with
  | trace a c member determinant =>
    obtain ⟨i,literal⟩:=member
    exact ⟨T.produce L.subtype H N (R.row (L.val.toRingHom : L→+*AlgebraicComplex) H i _ literal) a c
      (R.value (L.val.toRingHom : L→+*AlgebraicComplex) H i _ literal) determinant mapped⟩
  | x member =>
    rw [x_form] at member
    obtain ⟨i,literal⟩:=member
    exact ⟨T.produce L.subtype H N (R.row (L.val.toRingHom : L→+*AlgebraicComplex) H i _ literal) 0 1
      (R.value (L.val.toRingHom : L→+*AlgebraicComplex) H i _ literal) (by norm_num) mapped⟩

def produce (N : Macro H 3) (prime : Prime (⟨3,N.network.denote⟩ : AnySignature L))
    (resource : U.Witness (U.ambient L H)) : S.Output L.subtype H :=
  Classical.choice (exists_output L H N prime resource)

def fromOutput (N : NoXOrdinaryGraphAdjoin.Output H 3)
    (prime : Prime (⟨3,N.network.denote⟩ : AnySignature L))
    (resource : U.Witness (U.ambient L H)) : S.Output L.subtype H :=
  produce L H ⟨N.network,N.labels,N.exact,N.ordinary⟩ prime resource

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) (src : S.Data G)
def ofData (N : NoXOrdinaryGraphAdjoin.Output src.H 3)
    (prime : Prime (⟨3,N.network.denote⟩ : AnySignature src.K))
    (resource : U.Witness (S.family G src)) : S.Output src.K.subtype src.H :=
  fromOutput src.K src.H N prime resource


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsResourceTernary
end
