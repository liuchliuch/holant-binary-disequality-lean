import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedPredicateLeaf
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange
import Holant.ReedMuller.FlatNetwork.Tensor

/-! The concrete FlatOrZero predicate on the actual original-field rows.
Every split unit and original-port bijection is retained, so the strict
retained-counterexample minimum/restart machinery applies to this class.
No assertion about unretained graph outputs is made. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedFlatLeaf
open Holant Holant.Tractable Holant.Algebraic
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace R
export GlobalCloseCompletionRetainedPredicateLeaf (SplitClosed Minimum retained_bad_prime exists_minimum)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem flat_scale {n : ℕ} (f : Signature ℂ n) (flat : FlatOrZero f) (c : ℂ) (nonzero : c≠0) :
    FlatOrZero (fun x=>c*f x) := by
  rcases flat with rfl|⟨d,a,D,selfdual,rfl⟩
  · exact Or.inl (by funext x;simp)
  · refine Or.inr ⟨Units.mk0 c nonzero*d,a,D,selfdual,?_⟩
    funext x
    simp only [flatSignature,Units.val_mul,Units.val_mk0]
    split_ifs <;> simp

theorem flat_split {f a b : AnySignature ℂ} (split : ProperSplit f a b)
    (left : FlatOrZero a.2) (right : FlatOrZero b.2) : FlatOrZero f.2 := by
  let order : Fin (a.1+b.1)≃Fin f.1 := finSumFinEquiv.symm.trans split.ports
  have tensor := flatOrZero_tensor a.2 b.2 left right
  have reordered := flatOrZero_reindex order (Signature.tensor a.2 b.2) tensor
  have scaled := flat_scale _ reordered (split.scale : ℂ) split.scale.ne_zero
  convert scaled using 1
  funext x
  rw [split.equation]
  simp [order,Tensor.reindex,Signature.tensor]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def Predicate (f : AnySignature (OI.K G)) : Prop :=
  FlatOrZero (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f.2)

theorem split_closed : R.SplitClosed (Predicate G) := by
  intro f a b split left right
  exact flat_split (split.map (ClosurePhysicalBridge.complexEmbedding G)) left right

theorem retained_nonflat_prime (i : Fin P.count)
    (bad : ¬Predicate G ⟨P.arity i.val,P.table i⟩) :
    ∃g : AnySignature (OI.K G),g∈(P.trees i).leaves ∧ g∈P.family ∧ Prime g ∧
      g.1≤P.arity i.val ∧ ¬Predicate G g :=
  R.retained_bad_prime G P (Predicate G) (split_closed G) i bad

theorem exists_minimum (bad : ∃i : Fin P.count,¬Predicate G ⟨P.arity i.val,P.table i⟩) :
    Nonempty (R.Minimum G P (Predicate G)) :=
  R.exists_minimum G P (Predicate G) (split_closed G) bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedFlatLeaf
end
