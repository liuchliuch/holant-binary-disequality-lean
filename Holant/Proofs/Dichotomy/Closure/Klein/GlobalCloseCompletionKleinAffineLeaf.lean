import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardNonrealSource
import Holant.Tractable.AffineOperations

/-! A nonaffine retained row has a genuine nonaffine prime in its saved factor
 tree. The least such retained prime has finite retained minimality only;
 no closure of arbitrary network outputs or factor gadget access is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinAffineLeaf
open Holant Holant.Tractable Holant.Algebraic
open Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem affine_factorTree {L : Type*} [Field L] (phi : L→+*AlgebraicComplex)
    {f : AnySignature L} (tree : FactorTree f)
    (leaves : ∀g∈tree.leaves,Affine (RingHomRealization.mapSignature phi g.2)) :
    Affine (RingHomRealization.mapSignature phi f.2) := by
  induction tree with
  | leaf f prime => exact leaves f (by simp [FactorTree.leaves])
  | @split f a b split left right ihl ihr =>
    have hl := ihl (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inl hg)))
    have hr := ihr (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inr hg)))
    have h := ((hl.precompose (fun x i=>x (split.ports (.inl i)))
      (coordinates_isAffineMap (fun i=>split.ports (.inl i)))).mul
      (hr.precompose (fun x i=>x (split.ports (.inr i)))
        (coordinates_isAffineMap (fun i=>split.ports (.inr i))))).scale (phi (split.scale : L))
    convert h using 1
    funext x
    change phi (f.2 x)=_
    rw [split.equation,map_mul,map_mul]
    rfl

theorem nonaffine_leaf {L : Type*} [Field L] (phi : L→+*AlgebraicComplex)
    {f : AnySignature L} (tree : FactorTree f)
    (bad : ¬Affine (RingHomRealization.mapSignature phi f.2)) :
    ∃g∈tree.leaves,¬Affine (RingHomRealization.mapSignature phi g.2) := by
  classical
  by_contra h
  push Not at h
  exact bad (affine_factorTree phi tree h)

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def IsAffine (f : AnySignature (OI.K G)) : Prop :=
  Affine (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2)

theorem retained_nonaffine_prime (i : Fin P.count)
    (bad : ¬IsAffine G ⟨P.arity i.val,P.table i⟩) :
    ∃g : AnySignature (OI.K G),g∈(P.trees i).leaves ∧ g∈P.family ∧ Prime g ∧
      g.1≤P.arity i.val ∧ ¬IsAffine G g := by
  obtain ⟨g,hg,badg⟩ := nonaffine_leaf (ClosureSourceRows.embedding G) (P.trees i) bad
  exact ⟨g,hg,P.leavesRetained i g hg,(P.trees i).leaves_prime g hg,
    (P.trees i).leaf_arity_le g hg,badg⟩

structure Minimum where
  signature : AnySignature (OI.K G)
  retained : signature∈P.family
  prime : Prime signature
  bad : ¬IsAffine G signature
  minimum : ∀g∈P.family,Prime g→¬IsAffine G g→signature.1≤g.1

theorem exists_minimum (bad : ∃i : Fin P.count,¬IsAffine G ⟨P.arity i.val,P.table i⟩) :
    Nonempty (Minimum G P) := by
  classical
  obtain ⟨i,hi⟩ := bad
  obtain ⟨g,_,hg,hprime,_,hbad⟩ := retained_nonaffine_prime G P i hi
  have sizes : ∃n : ℕ,∃f : AnySignature (OI.K G),f∈P.family ∧ Prime f ∧ ¬IsAffine G f ∧ f.1=n :=
    ⟨g.1,g,hg,hprime,hbad,rfl⟩
  obtain ⟨f,hf,hp,ha,hn⟩ := Nat.find_spec sizes
  refine ⟨⟨f,hf,hp,ha,?_⟩⟩
  intro q hq hqp hqa
  rw [hn]
  exact Nat.find_min' sizes ⟨q,hq,hqp,hqa,rfl⟩

theorem Minimum.smaller_prime_affine (M : Minimum G P) (g : AnySignature (OI.K G))
    (retained : g∈P.family) (prime : Prime g) (smaller : g.1<M.signature.1) : IsAffine G g := by
  classical
  by_contra bad
  exact (Nat.not_le.mpr smaller) (M.minimum g retained prime bad)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinAffineLeaf
end
