import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPinnedProduct

/-! Source-side hypotheses for the unary-factor branch come from the actual
saved factor trees of zero caps. Every split scalar and port permutation is
preserved while reconstructing the coordinatewise product. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTrees
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (UnaryProduct cap)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

theorem join {f a b : AnySignature K} (s : ProperSplit f a b)
    (left : P.UnaryProduct a.2) (right : P.UnaryProduct b.2) : P.UnaryProduct f.2 := by
  classical
  obtain ⟨c,wa,ha⟩ := left
  obtain ⟨d,wb,hb⟩ := right
  let w : Fin f.1→Bool→K := fun i bit=>
    Sum.elim (fun j=>wa j bit) (fun j=>wb j bit) (s.ports.symm i)
  refine ⟨(s.scale : K)*c*d,w,?_⟩
  intro x
  rw [s.equation]
  dsimp only
  rw [ha,hb,←s.ports.prod_comp (fun i=>w i (x i)),Fintype.prod_sum_type]
  simp only [w,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  ring

theorem of_tree {f : AnySignature K} (t : FactorTree f)
    (unary : ∀g∈t.leaves,g.1=1) : P.UnaryProduct f.2 := by
  induction t with
  | leaf f prime=>
    have h : f.1=1 := unary f (by simp [FactorTree.leaves])
    rcases f with ⟨n,f⟩
    dsimp only at h
    subst n
    refine ⟨1,fun _ b=>f (fun _=>b),?_⟩
    intro x
    have hx : (fun _ : Fin 1=>x 0)=x := funext fun i=>congrArg x (Fin.eq_zero i).symm
    simp [hx]
  | split s a b ia ib=>
    exact join s (ia (fun g hg=>unary g (Multiset.mem_add.mpr (.inl hg))))
      (ib (fun g hg=>unary g (Multiset.mem_add.mpr (.inr hg))))

theorem reindex (f : Signature K n) (e : Equiv.Perm (Fin n)) (product : P.UnaryProduct f) :
    P.UnaryProduct (Tensor.reindex e f) := by
  obtain ⟨c,w,hw⟩ := product
  refine ⟨c,fun i b=>w (e.symm i) b,?_⟩
  intro x
  rw [Tensor.reindex,hw]
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp e (fun i=>w (e.symm i) (x i)))

/-- Reinserting the ignored capped variable contributes only a factor one.
Thus the canonical all-original-ports predicate is derived from the actual
smaller cap tensor, without treating a dummy variable as a source vertex. -/
theorem cap_zero_of_pin (f : Signature K (n+1)) (product : P.UnaryProduct (Signature.pin f false)) :
    P.UnaryProduct (P.cap 0 f) := by
  classical
  obtain ⟨c,w,hw⟩ := product
  refine ⟨c,Fin.cons (fun _=>1) w,?_⟩
  intro x
  have assignment : Function.update x 0 false=Fin.cons false (fun i=>x i.succ) := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp
    · simp
  change f (Function.update x 0 false)=_
  rw [assignment]
  change Signature.pin f false (fun i=>x i.succ)=_
  rw [hw]
  simp [Fin.prod_univ_succ]

theorem cap_zero_of_tree (f : Signature K (n+1))
    (t : FactorTree (⟨n,Signature.pin f false⟩ : AnySignature K))
    (unary : ∀g∈t.leaves,g.1=1) : P.UnaryProduct (P.cap 0 f) :=
  cap_zero_of_pin f (of_tree t unary)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTrees
end
