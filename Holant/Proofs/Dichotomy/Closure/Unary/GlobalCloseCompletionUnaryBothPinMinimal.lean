import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinFactors
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryWholeFamilySelector

/-! The least actual nonbinary prime is chosen inside the both-pin source.
Every genuinely smaller actual graph is then proved small by its own UPF;
all selected factors are exposed by actual complementary zero/one pins. No
minimality witness or classification callback is required from the caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinMinimal
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace W
export GlobalCloseCompletionUnaryWholeFamilySelector (row row_value tree large_exists)
end W
namespace F
export GlobalCloseCompletionUnaryBothPinFactors (exists_leaf)
export GlobalCloseCompletionUnaryHighSelector (leaf_arity_le)
export GlobalCloseCompletionUnaryPrimeSubgraph (zero_small)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1)
variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H))

def Available (m : ℕ) : Prop := 3≤m ∧ ∃N : NoXOrdinaryGraphAdjoin.Output H m,
  Prime (⟨m,N.network.denote⟩ : AnySignature L)

include pinsForm negative in
theorem exists_available : ∃m,Available L H m := by
  obtain ⟨i,positive,nonzero,g,member,large⟩:=W.large_exists L H negative
  obtain ⟨V,prime,c,hc,form⟩:=F.exists_leaf H pins (W.row L H i) pinsForm
    (by rwa [W.row_value]) (W.tree L H i nonzero) g member
  exact ⟨g.1,large,V,prime⟩

local instance : DecidablePred (Available L H) := Classical.decPred _

def arity : ℕ := Nat.find (exists_available L H pins pinsForm negative)
theorem large : 3≤arity L H pins pinsForm negative := (Nat.find_spec (exists_available L H pins pinsForm negative)).1

def graph : NoXOrdinaryGraphAdjoin.Output H (arity L H pins pinsForm negative) :=
  Classical.choose (Nat.find_spec (exists_available L H pins pinsForm negative)).2

theorem prime : Prime (⟨arity L H pins pinsForm negative,(graph L H pins pinsForm negative).network.denote⟩ : AnySignature L) :=
  Classical.choose_spec (Nat.find_spec (exists_available L H pins pinsForm negative)).2

theorem least (m : ℕ) (big : 3≤m) (N : NoXOrdinaryGraphAdjoin.Output H m)
    (prime : Prime (⟨m,N.network.denote⟩ : AnySignature L)) : arity L H pins pinsForm negative≤m :=
  Nat.find_min' (exists_available L H pins pinsForm negative) ⟨big,N,prime⟩

theorem small {m : ℕ} (bound : m<arity L H pins pinsForm negative)
    (N : NoXOrdinaryGraphAdjoin.Output H m) :
    Signature.TensorClosure (fun n (_ : Signature L n)=>n≤2) N.network.denote := by
  classical
  by_cases tiny : m≤2
  · let D:=ClosureSmallArity.Packed.single (⟨m,N.network.denote⟩ : AnySignature L)
    exact ⟨D.decomposition,(fun _=>tiny),D.decomposition_value⟩
  by_cases zero : N.network.denote=0
  · rw [zero]
    exact F.zero_small (by omega)
  obtain ⟨t⟩:=exists_factorTree (⟨m,N.network.denote⟩ : AnySignature L) zero
  apply ClosureSmallArity.tensorClosure_of_saved_tree t (fun n (_ : Signature L n)=>n≤2)
  intro g member
  by_contra large
  obtain ⟨V,pv,c,hc,form⟩:=F.exists_leaf H pins N pinsForm zero t g member
  have min:=least L H pins pinsForm negative g.1 (by omega) V pv
  have max:=F.leaf_arity_le t member
  change g.1≤m at max
  omega


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinMinimal
end
