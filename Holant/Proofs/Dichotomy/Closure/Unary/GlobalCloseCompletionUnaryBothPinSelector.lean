import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinHighUnary
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinHighBinary
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinQ4

/-! The genuine both-pin selector ends in an actual ternary prime or actual
unsigned nonsingular paired quaternary. The least nonbinary prime, supported
word, ordered interactions, all pin assignments and every equality loop are
chosen internally. The already present opposite pin is never a terminal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinSelector
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.FinitePGL2.Stabilization
namespace M
export GlobalCloseCompletionUnaryBothPinMinimal (arity graph prime large)
end M
namespace D
export GlobalCloseCompletionUnaryBothPinNormalized (Data ofPrime)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1)
variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H))

include pinsForm negative in
theorem rank_bound {n : ℕ} (N : D.Data H n) (size : n=M.arity L H pins pinsForm negative) : n≤4 := by
  by_contra high
  obtain ⟨t,rfl⟩ : ∃t,n=t+4 := ⟨n-4,by omega⟩
  obtain ⟨V,order⟩:=GlobalCloseCompletionUnaryBothPinOrdering.exists_order H N
  rcases order with unary|binary
  · exact GlobalCloseCompletionUnaryBothPinHighUnary.impossible L H pins pinsForm negative (by omega) V size unary
  · exact GlobalCloseCompletionUnaryBothPinHighBinary.impossible L H pins pinsForm negative (by omega) V size binary

inductive Output : Type where
  | ternary (graph : NoXOrdinaryGraphAdjoin.Output H 3)
      (prime : Prime (⟨3,graph.network.denote⟩ : AnySignature L))
  | paired (output : GlobalCloseCompletionUnarySignedPairConversion.Output (H:=H))

def ofThree {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H n)
    (prime : Prime (⟨n,N.network.denote⟩ : AnySignature L)) (arity : n=3) : Output L H := by
  subst n
  exact .ternary N prime

def ofFour {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H n)
    (prime : Prime (⟨n,N.network.denote⟩ : AnySignature L)) (arity : n=4)
    (size : n=M.arity L H pins pinsForm negative) : Output L H := by
  subst n
  exact .paired (GlobalCloseCompletionUnaryBothPinQ4.produce L H pins pinsForm negative
    (D.ofPrime H N prime) size)

def produce : Output L H := by
  classical
  let N:=M.graph L H pins pinsForm negative
  have prime:=M.prime L H pins pinsForm negative
  have lower:=M.large L H pins pinsForm negative
  have upper:=rank_bound L H pins pinsForm negative (D.ofPrime H N prime) rfl
  by_cases three : M.arity L H pins pinsForm negative=3
  · exact ofThree L H N prime three
  · have four : M.arity L H pins pinsForm negative=4 := by omega
    exact ofFour L H pins pinsForm negative N prime four rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinSelector
end
