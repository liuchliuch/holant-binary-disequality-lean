import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedPredicateRestart
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange
import Holant.ReedMuller.CharacterFlat.Tensor

/-! Character-flatness after the original embedding is genuinely closed under
ProperSplit. The retained leaf and minimum selectors therefore apply, including
all split units and literal original port bijections. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedCharacterLeaf
open Holant Holant.Tractable Holant.Algebraic
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace R
export GlobalCloseCompletionRetainedPredicateLeaf (SplitClosed Minimum retained_bad_prime exists_minimum)
end R
namespace S
export GlobalCloseCompletionRetainedPredicateRestart (finalPalette exists_strict_minimum)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem character_split {f a b : AnySignature ℂ} (split : ProperSplit f a b)
    (left : CFlat a.2) (right : CFlat b.2) : CFlat f.2 := by
  let order : Fin (a.1+b.1)≃Fin f.1 := finSumFinEquiv.symm.trans split.ports
  have tensor := CFlat.tensor a.2 b.2 left right
  have reordered := CFlat.reindex order (Signature.tensor a.2 b.2) tensor
  have scaled := CFlat.smul _ reordered (split.scale : ℂ)
  convert scaled using 1
  funext x
  rw [split.equation]
  simp [order,Tensor.reindex,Signature.tensor]

theorem zeroary (f : Signature ℂ 0) : CFlat f := by
  by_cases hz : f Fin.elim0=0
  · left
    funext x
    exact (congrArg f (Subsingleton.elim x Fin.elim0)).trans hz
  · right
    refine ⟨Units.mk0 (f Fin.elim0) hz,0,⊥,0,?_,?_⟩
    · intro x
      have hx : x=0 := Subsingleton.elim _ _
      simp [hx,dot]
    · funext x
      have hx : vectorWord x=(0 : BinaryVector 0) := Subsingleton.elim _ _
      simp only [signature,value,hx,sub_zero,Submodule.zero_mem,ite_true,
        LinearMap.zero_apply,sign_zero,mul_one,Units.val_mk0]
      exact congrArg f (Subsingleton.elim _ _)

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def Predicate (f : AnySignature (OI.K G)) : Prop :=
  CFlat (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f.2)

theorem split_closed : R.SplitClosed (Predicate G) := by
  intro f a b split left right
  exact character_split (split.map (ClosurePhysicalBridge.complexEmbedding G)) left right

theorem retained_noncharacter_prime (i : Fin P.count)
    (bad : ¬Predicate G ⟨P.arity i.val,P.table i⟩) :
    ∃g : AnySignature (OI.K G),g∈(P.trees i).leaves ∧ g∈P.family ∧ Prime g ∧
      g.1≤P.arity i.val ∧ ¬Predicate G g :=
  R.retained_bad_prime G P (Predicate G) (split_closed G) i bad

theorem exists_minimum (bad : ∃i : Fin P.count,¬Predicate G ⟨P.arity i.val,P.table i⟩) :
    Nonempty (R.Minimum G P (Predicate G)) :=
  R.exists_minimum G P (Predicate G) (split_closed G) bad

theorem exists_strict_minimum (q : AnySignature (OI.K G)) (nonzero : q.2≠0) (positive : 0<q.1)
    (actual : Gadget.Realizes P.family .disequality q.2) (bad : ¬Predicate G q)
    (old : R.Minimum G P (Predicate G)) (smaller : q.1<old.signature.1) :
    ∃new : R.Minimum G (S.finalPalette G P q nonzero positive actual) (Predicate G),
      new.signature.1<old.signature.1 :=
  S.exists_strict_minimum G P q nonzero positive actual (Predicate G) (split_closed G) bad old smaller


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedCharacterLeaf
end
