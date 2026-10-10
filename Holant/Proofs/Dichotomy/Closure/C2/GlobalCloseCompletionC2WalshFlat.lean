import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2HigherDeck

/-! Every supported Walsh coefficient of a literal I/X matching has the
same square. This records the stronger C2 information lost by the generic
weighted I/X-span deck, using its actual binary factors and original scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2WalshFlat
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
open Holant.ReedMuller.CoefficientAtlas Holant.ReedMuller.FixedCoreDeck
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open GlobalCloseCompletionC2TensorMatching GlobalCloseCompletionC2SafeSymmetry
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false

theorem binary_square (p a b : Bool) (live : binaryWalsh (originalC2Binary p) a b≠0) :
    binaryWalsh (originalC2Binary p) a b ^ 2=binaryWalsh (originalC2Binary p) false false ^ 2 := by
  cases p <;> cases a <;> cases b
  all_goals norm_num [binaryWalsh,originalC2Binary,Matrix.one_apply,X,Signature.equality,Signature.disequality,walshInverse,walshKernel] at live
  all_goals norm_num [binaryWalsh,originalC2Binary,Matrix.one_apply,X,Signature.equality,Signature.disequality,walshInverse,walshKernel]

theorem literal_square {n : ℕ} (f : Signature ℂ n) (literal : LiteralMatching f)
    (x : Fin n→Bool) (live : walsh f x≠0) : (walsh f x)^2=(walsh f (fun _=>false))^2 := by
  rcases literal with zero|⟨r,ports,label,c,_hc,form⟩
  · rw [zero] at live
    simp [walsh,Signature.coordinateAction] at live
  · rw [form] at live ⊢
    have W : walsh (productValue ports (fun i=>originalC2Binary (label i)) c)=
        productValue ports (fun i=>binaryWalsh (originalC2Binary (label i))) c := by
      exact coordinateAction_productValue ports walshInverse _ c
    rw [W] at live ⊢
    have factors : ∀i,binaryWalsh (originalC2Binary (label i)) (x (ports (i,false))) (x (ports (i,true)))≠0 := by
      intro i
      exact (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp live).2) i (Finset.mem_univ i)
    simp only [productValue,mul_pow,←Finset.prod_pow]
    apply congrArg (c^2*·)
    apply Finset.prod_congr rfl
    intro i _
    exact binary_square _ _ _ (factors i)

theorem walsh_contract {n : ℕ} (f : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) :
    walsh (Signature.contract Signature.equality (Tensor.reindex e.symm f))=
      fun x=>2*Signature.contract Signature.equality (Tensor.reindex e.symm (walsh f)) x := by
  have h : Signature.contract Signature.equality (Tensor.reindex e.symm f)=
      Signature.coordinateAction (fun _=>walshKernel)
        (fun x=>2*Signature.contract Signature.equality (Tensor.reindex e.symm (walsh f)) x) := by
    conv_lhs => rw [←physical_of_walsh f]
    rw [←coordinateAction_reindex,coordinateAction_contract,walsh_pullback_equality,contract_scale_kernel]
  rw [h,walsh_of_physical]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2WalshFlat
end
