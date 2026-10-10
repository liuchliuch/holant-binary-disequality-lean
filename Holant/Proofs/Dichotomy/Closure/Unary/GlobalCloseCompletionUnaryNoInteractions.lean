import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductInteraction
import Holant.Proofs.FiniteGroups.Stabilization.BinaryPrimes

/-! Absence of anchored binary interactions is the actual unary-factor
branch test. Along each saved split, a child minor is multiplied by a
nonzero complementary-origin square. Thus a small saved factor tree with
no interactions reconstructs a coordinatewise unary product internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryNoInteractions
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (UnaryProduct single)
export GlobalCloseCompletionUnaryProductTrees (join)
end P
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor double)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K]

def NoInteractions {n : ℕ} (f : Signature K n) : Prop := ∀i j,i≠j→I.minor f i j=0

def swap {f a b : AnySignature K} (s : ProperSplit f a b) : ProperSplit f b a where
  left_pos:=s.right_pos
  right_pos:=s.left_pos
  ports:=(Equiv.sumComm _ _).trans s.ports
  scale:=s.scale
  equation:=by
    rw [s.equation]
    funext x
    change (s.scale : K)*(a.2 _*b.2 _)=(s.scale : K)*(b.2 _*a.2 _)
    rw [mul_comm (a.2 _) (b.2 _)]
    rfl

theorem split_origin {f a b : AnySignature K} (s : ProperSplit f a b)
    (origin : f.2 (fun _=>false)≠0) : a.2 (fun _=>false)≠0 ∧ b.2 (fun _=>false)≠0 := by
  rw [s.equation] at origin
  exact mul_ne_zero_iff.mp (mul_ne_zero_iff.mp origin).2

theorem split_minor {f a b : AnySignature K} (s : ProperSplit f a b) (i j : Fin a.1) :
    I.minor f.2 (s.ports (.inl i)) (s.ports (.inl j))=
      ((s.scale : K)*b.2 (fun _=>false))^2*I.minor a.2 i j := by
  have singleLeft (i : Fin a.1) :
      (fun k=>P.single (s.ports (.inl i)) (s.ports (.inl k)))=P.single i := by
    funext k
    simp [P.single,Function.update,Equiv.apply_eq_iff_eq]
  have singleRight (i : Fin a.1) :
      (fun k=>P.single (s.ports (.inl i)) (s.ports (.inr k)))=(fun _=>false) := by
    funext k
    simp [P.single,Function.update,Equiv.apply_eq_iff_eq]
  have doubleLeft :
      (fun k=>I.double (s.ports (.inl i)) (s.ports (.inl j)) (s.ports (.inl k)))=I.double i j := by
    funext k
    simp [I.double,P.single,Function.update,Equiv.apply_eq_iff_eq]
  have doubleRight :
      (fun k=>I.double (s.ports (.inl i)) (s.ports (.inl j)) (s.ports (.inr k)))=(fun _=>false) := by
    funext k
    simp [I.double,P.single,Function.update,Equiv.apply_eq_iff_eq]
  unfold I.minor
  rw [s.equation]
  dsimp only
  rw [singleLeft,singleLeft,singleRight,singleRight,doubleLeft,doubleRight]
  ring

theorem split_noInteractions {f a b : AnySignature K} (s : ProperSplit f a b)
    (origin : f.2 (fun _=>false)≠0) (none : NoInteractions f.2) : NoInteractions a.2 := by
  intro i j different
  have h:=none (s.ports (.inl i)) (s.ports (.inl j)) (by
    intro equal
    exact different (Sum.inl.inj (s.ports.injective equal)))
  rw [split_minor] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero 2 (mul_ne_zero s.scale.ne_zero (split_origin s origin).2))

theorem small_product {n : ℕ} (f : Signature K n) (small : n≤2)
    (origin : f (fun _=>false)≠0) (none : NoInteractions f) : P.UnaryProduct f := by
  cases n with
  | zero=>
    refine ⟨f (fun _=>false),fun i=>Fin.elim0 i,?_⟩
    intro x
    have hx : x=(fun _=>false) := funext fun i=>Fin.elim0 i
    simp [hx]
  | succ n=>
    cases n with
    | zero=>
      refine ⟨1,fun _ b=>f (fun _=>b),?_⟩
      intro x
      have hx : (fun _ : Fin 1=>x 0)=x := funext fun i=>congrArg x (Fin.eq_zero i).symm
      simp [hx]
    | succ n=>
      have hn : n=0 := by omega
      subst n
      have nonzero : binaryMatrix f≠0 := by
        intro zero
        apply origin
        have h:=congrFun (congrFun zero false) false
        have bottom : (![false,false] : Fin 2→Bool)=(fun _=>false) := by
          funext i
          fin_cases i <;>rfl
        change f ![false,false]=0 at h
        rwa [bottom] at h
      have determinant : Matrix.det (binaryMatrix f)=0 := by
        rw [binary_det_formula]
        have h:=none 0 1 (by decide)
        have h0 : (fun _ : Fin 2=>false)=![false,false] := by funext i;fin_cases i <;>rfl
        have hi : P.single (0 : Fin 2)=![true,false] := by funext i;fin_cases i <;>decide
        have hj : P.single (1 : Fin 2)=![false,true] := by funext i;fin_cases i <;>decide
        have hij : I.double (0 : Fin 2) 1=![true,true] := by funext i;fin_cases i <;>decide
        simpa only [I.minor,h0,hi,hj,hij,binaryMatrix,mul_comm] using h
      obtain ⟨u,v,equation⟩:=singular_binary_split (binaryMatrix f) nonzero determinant
      refine ⟨1,![u,v],?_⟩
      intro x
      have hx : ![x 0,x 1]=x := by funext i;fin_cases i <;>rfl
      simpa [binaryMatrix,hx,Fin.prod_univ_two] using equation (x 0) (x 1)

theorem of_tree {f : AnySignature K} (t : FactorTree f)
    (small : ∀g∈t.leaves,g.1≤2) (origin : f.2 (fun _=>false)≠0)
    (none : NoInteractions f.2) : P.UnaryProduct f.2 := by
  induction t with
  | leaf f prime=>exact small_product f.2 (small f (by simp [FactorTree.leaves])) origin none
  | split s a b ia ib=>
    exact P.join s
      (ia (fun g hg=>small g (Multiset.mem_add.mpr (.inl hg)))
        (split_origin s origin).1 (split_noInteractions s origin none))
      (ib (fun g hg=>small g (Multiset.mem_add.mpr (.inr hg)))
        (split_origin s origin).2 (split_noInteractions (swap s) origin none))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryNoInteractions
end
