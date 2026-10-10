import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinAffineLeaf

/-! Minimal counterexamples inside a genuine retained palette. A structural
split-closure proof is explicit, so the predicate can be Affine in any one
fixed source coordinate system. These statements do not assert that arbitrary
new graph outputs already belong to the palette. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedPredicateLeaf
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

variable {L : Type*} [Field L]
def SplitClosed (C : AnySignature L→Prop) : Prop :=
  ∀{f a b : AnySignature L},ProperSplit f a b→C a→C b→C f

theorem factorTree (C : AnySignature L→Prop) (closed : SplitClosed C)
    {f : AnySignature L} (tree : FactorTree f) (leaves : ∀g∈tree.leaves,C g) : C f := by
  induction tree with
  | leaf f prime => exact leaves f (by simp [FactorTree.leaves])
  | @split f a b split left right ihl ihr =>
    exact closed split
      (ihl (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inl hg))))
      (ihr (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inr hg))))

theorem bad_leaf (C : AnySignature L→Prop) (closed : SplitClosed C)
    {f : AnySignature L} (tree : FactorTree f) (bad : ¬C f) : ∃g∈tree.leaves,¬C g := by
  classical
  by_contra h
  push Not at h
  exact bad (factorTree C closed tree h)

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (C : AnySignature (OI.K G)→Prop)

theorem retained_bad_prime (closed : SplitClosed C) (i : Fin P.count)
    (bad : ¬C ⟨P.arity i.val,P.table i⟩) :
    ∃g : AnySignature (OI.K G),g∈(P.trees i).leaves ∧ g∈P.family ∧ Prime g ∧
      g.1≤P.arity i.val ∧ ¬C g := by
  obtain ⟨g,hg,badg⟩ := bad_leaf C closed (P.trees i) bad
  exact ⟨g,hg,P.leavesRetained i g hg,(P.trees i).leaves_prime g hg,
    (P.trees i).leaf_arity_le g hg,badg⟩

structure Minimum where
  signature : AnySignature (OI.K G)
  retained : signature∈P.family
  prime : Prime signature
  bad : ¬C signature
  minimum : ∀g∈P.family,Prime g→¬C g→signature.1≤g.1

theorem exists_minimum (closed : SplitClosed C)
    (bad : ∃i : Fin P.count,¬C ⟨P.arity i.val,P.table i⟩) : Nonempty (Minimum G P C) := by
  classical
  obtain ⟨i,hi⟩ := bad
  obtain ⟨g,_,hg,hprime,_,hbad⟩ := retained_bad_prime G P C closed i hi
  have sizes : ∃n : ℕ,∃f : AnySignature (OI.K G),f∈P.family ∧ Prime f ∧ ¬C f ∧ f.1=n :=
    ⟨g.1,g,hg,hprime,hbad,rfl⟩
  obtain ⟨f,hf,hp,ha,hn⟩ := Nat.find_spec sizes
  refine ⟨⟨f,hf,hp,ha,?_⟩⟩
  intro q hq hqp hqa
  rw [hn]
  exact Nat.find_min' sizes ⟨q,hq,hqp,hqa,rfl⟩

theorem Minimum.smaller_prime (M : Minimum G P C) (g : AnySignature (OI.K G))
    (retained : g∈P.family) (prime : Prime g) (smaller : g.1<M.signature.1) : C g := by
  classical
  by_contra bad
  exact (Nat.not_le.mpr smaller) (M.minimum g retained prime bad)

theorem Minimum.arity_le_retained (M : Minimum G P C) (closed : SplitClosed C)
    (g : AnySignature (OI.K G)) (retained : g∈P.family) (bad : ¬C g) : M.signature.1≤g.1 := by
  obtain ⟨i,rfl⟩ := retained
  obtain ⟨q,_,hq,hprime,small,hbad⟩ := retained_bad_prime G P C closed i bad
  exact (M.minimum q hq hprime hbad).trans small

theorem Minimum.smaller_retained (M : Minimum G P C) (closed : SplitClosed C)
    (g : AnySignature (OI.K G)) (retained : g∈P.family) (smaller : g.1<M.signature.1) : C g := by
  classical
  by_contra bad
  exact (Nat.not_le.mpr smaller) (M.arity_le_retained G P C closed g retained bad)

theorem Minimum.strict_of_new_bad (M : Minimum G P C) (Q : Palette G) (N : Minimum G Q C)
    (closed : SplitClosed C) (g : AnySignature (OI.K G)) (retained : g∈Q.family)
    (bad : ¬C g) (smaller : g.1<M.signature.1) : N.signature.1<M.signature.1 :=
  (N.arity_le_retained G Q C closed g retained bad).trans_lt smaller


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedPredicateLeaf
end
