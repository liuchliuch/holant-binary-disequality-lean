import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedPredicateRestart
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinAffineCoordinates

/-! A nonprime actual nonaffine output may have the same arity as the old bad
minimum. Its complete factor batch nevertheless exposes a strictly smaller
nonaffine prime, with every old row and saved tree retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFactorRestart
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace A
export GlobalCloseCompletionKleinAffineLeaf (IsAffine nonaffine_leaf)
end A
namespace L
export GlobalCloseCompletionRetainedPredicateLeaf (SplitClosed Minimum)
end L
namespace R
export GlobalCloseCompletionRetainedPredicateRestart (finalPalette rootLabel root_saved minimum_exists)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem leaf_strict_of_nonprime {K : Type*} [Field K] {q : AnySignature K}
    (tree : FactorTree q) (notPrime : ¬Prime q) (g : AnySignature K) (member : g∈tree.leaves) :
    g.1<q.1 := by
  cases tree with
  | leaf q prime => exact (notPrime prime).elim
  | split split left right =>
    rcases Multiset.mem_add.mp member with hl|hr
    · exact (left.leaf_arity_le g hl).trans_lt split.left_lt
    · exact (right.leaf_arity_le g hr).trans_lt split.right_lt

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

theorem affine_split_closed : L.SplitClosed (A.IsAffine G) := by
  intro f a b split left right
  exact GlobalCloseCompletionKleinAffineCoordinates.affine_split (split.map (ClosureSourceRows.embedding G)) left right

variable (q : AnySignature (OI.K G)) (nonzero : q.2≠0) (positive : 0<q.1)
variable (actual : Gadget.Realizes P.family .disequality q.2)

include nonzero positive actual in
theorem split_strict (old : L.Minimum G P (A.IsAffine G)) (bad : ¬A.IsAffine G q)
    (notPrime : ¬Prime q) (bound : q.1≤old.signature.1) :
    ∃new : L.Minimum G (R.finalPalette G P q nonzero positive actual) (A.IsAffine G),
      new.signature.1<old.signature.1 := by
  obtain ⟨new⟩ := R.minimum_exists G P q nonzero positive actual (A.IsAffine G) (affine_split_closed G) bad
  let tree := RetainedFactorCatalogue.tree G q nonzero
  obtain ⟨g,member,badg⟩ := A.nonaffine_leaf (ClosureSourceRows.embedding G) tree bad
  have root := R.root_saved G P q nonzero positive actual
  have leaves := congrArg (fun z : TreeOccurrence (OI.K G)=>z.2.leaves) root
  change ((R.finalPalette G P q nonzero positive actual).trees
    (R.rootLabel G P q nonzero positive actual)).leaves=tree.leaves at leaves
  have memberNew : g∈((R.finalPalette G P q nonzero positive actual).trees
      (R.rootLabel G P q nonzero positive actual)).leaves := by
    rw [leaves]
    exact member
  have retained := (R.finalPalette G P q nonzero positive actual).leavesRetained
    (R.rootLabel G P q nonzero positive actual) g memberNew
  have smaller := leaf_strict_of_nonprime tree notPrime g member
  exact ⟨new,(new.minimum g retained (tree.leaves_prime g member) badg).trans_lt (smaller.trans_le bound)⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFactorRestart
end
