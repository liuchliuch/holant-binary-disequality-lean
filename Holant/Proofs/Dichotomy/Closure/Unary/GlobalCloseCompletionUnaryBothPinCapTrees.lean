import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinProjection
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTernarySmallCubic

/-! Saved cap trees for the actual least nonbinary prime. Their small leaves
are proved by physical complementary-pin extraction and minimality. A
semantic mask transports the same split tree, with no fake source gates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinCapTrees
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace F
export GlobalCloseCompletionUnaryBitFlip (value word split prime)
end F
namespace B
export GlobalCloseCompletionUnaryBitFlipPins (cap cap_flip project)
end B
namespace P
export GlobalCloseCompletionUnaryBothPinProjection (output denote signed_denote split)
end P
namespace M
export GlobalCloseCompletionUnaryBothPinMinimal (arity least)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option Elab.async false
attribute [local irreducible] GlobalCloseCompletionUnaryBothPinMinimal.arity
  GlobalCloseCompletionUnaryBothPinProjection.output GlobalCloseCompletionUnaryBothPinProjection.split
variable {K : Type} [Field K]

def flipTreeAux : {f : AnySignature K}→(t : FactorTree f)→(mask : Fin f.1→Bool)→
    FactorTree (⟨f.1,F.value mask f.2⟩ : AnySignature K)
  | _,.leaf f hp,mask=>.leaf _ (F.prime mask f.2 hp)
  | _,.split s ta tb,mask=>.split (F.split s mask)
      (flipTreeAux ta (fun i=>mask (s.ports (.inl i))))
      (flipTreeAux tb (fun i=>mask (s.ports (.inr i))))

def flipTree {f : AnySignature K} (mask : Fin f.1→Bool) (t : FactorTree f) :
    FactorTree (⟨f.1,F.value mask f.2⟩ : AnySignature K) := flipTreeAux t mask

theorem flipTree_small {f : AnySignature K} (t : FactorTree f)
    (small : ∀g∈t.leaves,g.1≤2) (mask : Fin f.1→Bool) : ∀g∈(flipTree mask t).leaves,g.1≤2 := by
  induction t with
  | leaf f hp=>
    intro g member
    have same : g=(⟨f.1,F.value mask f.2⟩ : AnySignature K) := by
      simpa only [flipTree,flipTreeAux,FactorTree.leaves,Multiset.mem_singleton] using member
    rw [same]
    exact small f (by simp [FactorTree.leaves])
  | split s ta tb ia ib=>
    intro g member
    change g∈(flipTree (fun i=>mask (s.ports (.inl i))) ta).leaves+
      (flipTree (fun i=>mask (s.ports (.inr i))) tb).leaves at member
    rcases Multiset.mem_add.mp member with left|right
    · exact ia (fun g hg=>small g (Multiset.mem_add.mpr (.inl hg))) _ g left
    · exact ib (fun g hg=>small g (Multiset.mem_add.mpr (.inr hg))) _ g right

def castTree {f g : AnySignature K} (eqn : f=g) (t : FactorTree f) : FactorTree g := eqn ▸t

theorem castTree_leaves {f g : AnySignature K} (eqn : f=g) (t : FactorTree f) : (castTree eqn t).leaves=t.leaves := by
  cases eqn
  rfl

theorem project_origin {n : ℕ} (f : Signature K (n+1)) (i : Fin (n+1)) :
    B.project i false f (fun _=>false)=f (fun _=>false) := by
  unfold B.project Tensor.reindex
  congr 1
  funext j
  generalize Equiv.swap (0 : Fin (n+1)) i j=k
  exact Fin.cases rfl (fun _=>rfl) k

variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1)
variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H))

include pinsForm negative in
theorem actual_tree_small {m : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H m)
    (bound : m<M.arity L H pins pinsForm negative) (nonzero : N.network.denote≠0)
    (t : FactorTree (⟨m,N.network.denote⟩ : AnySignature L)) : ∀g∈t.leaves,g.1≤2 := by
  intro g member
  by_contra big
  obtain ⟨V,prime,c,hc,form⟩:=GlobalCloseCompletionUnaryBothPinFactors.exists_leaf
    H pins N pinsForm nonzero t g member
  have lower:=M.least L H pins pinsForm negative g.1 (by omega) V prime
  have upper:=GlobalCloseCompletionUnaryHighSelector.leaf_arity_le t member
  change g.1≤m at upper
  omega

variable {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H (n+1))
variable (bound : n<M.arity L H pins pinsForm negative)
variable (mask : Fin (n+1)→Bool)
variable (origin : F.value mask N.network.denote (fun _=>false)≠0)

include pinsForm origin in
theorem zero_cap_nonzero (i : Fin (n+1)) : (P.output H pins N i (mask i)).network.denote≠0 := by
  intro zero
  have h:=P.signed_denote H pins pinsForm N mask i false
  simp only [Bool.false_xor] at h
  rw [zero,GlobalCloseCompletionUnaryBitFlip.value_zero] at h
  have hz:=congrFun h (fun _=>false)
  rw [project_origin] at hz
  exact origin hz

include pinsForm negative bound origin in
theorem cap_tree_exists (positive : 0<n) (i : Fin (n+1)) :
    ∃t : FactorTree (⟨n+1,B.cap i false (F.value mask N.network.denote)⟩ : AnySignature L),
      ∀g∈t.leaves,g.1≤2 := by
  have nonzero:=zero_cap_nonzero L H pins pinsForm N mask origin i
  obtain ⟨t⟩:=exists_factorTree (⟨n,(P.output H pins N i (mask i)).network.denote⟩ : AnySignature L) nonzero
  have tiny:=actual_tree_small L H pins pinsForm negative (P.output H pins N i (mask i)) bound nonzero t
  let s:=P.split H pins pinsForm N positive i (mask i)
  let left : AnySignature L:=⟨1,F.value (fun j=>mask (s.ports (.inl j))) (fun _=>1)⟩
  let right : AnySignature L:=⟨n,F.value (fun j=>mask (s.ports (.inr j)))
    (P.output H pins N i (mask i)).network.denote⟩
  let transformed:=F.split s mask
  have root_eq : B.cap i false (F.value mask N.network.denote)=
      F.value mask (B.cap i (mask i) N.network.denote) := by
    simpa only [Bool.false_xor] using B.cap_flip mask N.network.denote i false
  let split : ProperSplit (⟨n+1,B.cap i false (F.value mask N.network.denote)⟩ : AnySignature L) left right := {
    left_pos:=transformed.left_pos
    right_pos:=transformed.right_pos
    ports:=transformed.ports
    scale:=transformed.scale
    equation:=root_eq.trans transformed.equation }
  let leftTree : FactorTree left:=.leaf left (F.prime _ _ (GlobalCloseCompletionUnaryZeroCapTrees.unary_prime (K:=L)))
  let rightTree : FactorTree right:=flipTree (fun j=>mask (s.ports (.inr j))) t
  refine ⟨FactorTree.split split leftTree rightTree,?_⟩
  intro g member
  rcases Multiset.mem_add.mp member with hl|hr
  · have same : g=left := by simpa only [leftTree,FactorTree.leaves,Multiset.mem_singleton] using hl
    rw [same]
    change 1≤2
    decide
  · exact flipTree_small t tiny _ g hr

include pinsForm negative bound origin in
def capTree (positive : 0<n) (i : Fin (n+1)) :
    FactorTree (⟨n+1,B.cap i false (F.value mask N.network.denote)⟩ : AnySignature L) :=
  Classical.choose (cap_tree_exists L H pins pinsForm negative N bound mask origin positive i)

include pinsForm negative bound origin in
theorem capTree_small (positive : 0<n) (i : Fin (n+1)) :
    ∀g∈(capTree L H pins pinsForm negative N bound mask origin positive i).leaves,g.1≤2 :=
  Classical.choose_spec (cap_tree_exists L H pins pinsForm negative N bound mask origin positive i)

include pinsForm negative in
theorem cubic (N : NoXOrdinaryGraphAdjoin.Output H 4) (bound : 3<M.arity L H pins pinsForm negative)
    (mask : Fin 4→Bool) (i : Fin 4) (bit : Bool) :
    GlobalCloseCompletionUnaryTernarySmallCubic.cubic (B.project i bit (F.value mask N.network.denote))=0 := by
  let V:=P.output H pins N i (bit^^mask i)
  by_cases nonzero : V.network.denote≠0
  · obtain ⟨t⟩:=exists_factorTree (⟨3,V.network.denote⟩ : AnySignature L) nonzero
    have small:=actual_tree_small L H pins pinsForm negative V bound nonzero t
    rw [P.signed_denote H pins pinsForm N mask i bit]
    exact GlobalCloseCompletionUnaryTernarySmallCubic.of_tree _ (flipTree _ t) (flipTree_small t small _)
  · have zero : V.network.denote=0:=not_not.mp nonzero
    rw [P.signed_denote H pins pinsForm N mask i bit,show (P.output H pins N i (bit^^mask i)).network.denote=0 from zero]
    simp [GlobalCloseCompletionUnaryBitFlip.value_zero,GlobalCloseCompletionUnaryTernarySmallCubic.cubic]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinCapTrees
end
