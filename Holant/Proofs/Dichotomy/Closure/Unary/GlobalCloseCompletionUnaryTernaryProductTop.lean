import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTernarySmallCubic

/-! The nonzero-singleton quaternary base produces a ternary unary-times-
binary tensor plus a top correction. Its cubic is exactly correction times
the origin squared, so a nonzero origin proves primality with no rank test
or ternary classifier supplied. Zero origin still leaves a nonzero graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTernaryProductTop
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace C
export GlobalCloseCompletionUnaryTernarySmallCubic (cubic proper_split)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K]

theorem prime_of_cubic (f : Signature K 3) (nonzero : C.cubic f≠0) :
    Prime (⟨3,f⟩ : AnySignature K) := by
  refine ⟨?_,?_⟩
  · intro zero
    change f=0 at zero
    apply nonzero
    simp [zero,C.cubic]
  · rintro ⟨a,b,⟨split⟩⟩
    exact nonzero (C.proper_split f split)

def value (u : Bool→K) (B : Bool→Bool→K) (d : K) : Signature K 3 :=
  fun x=>u (x 0)*B (x 1) (x 2)+if x=(fun _=>true) then d else 0

theorem cubic (u : Bool→K) (B : Bool→Bool→K) (d : K) :
    C.cubic (value u B d)=d*(u false*B false false)^2 := by
  simp [C.cubic,value,funext_iff,Fin.forall_fin_succ]
  ring

theorem origin (u : Bool→K) (B : Bool→Bool→K) (d : K) :
    value u B d (fun _=>false)=u false*B false false := by
  simp [value,funext_iff,Fin.forall_fin_succ]

theorem prime (u : Bool→K) (B : Bool→Bool→K) (d : K)
    (first : value u B d (fun _=>false)≠0) (correction : d≠0) :
    Prime (⟨3,value u B d⟩ : AnySignature K) := by
  apply prime_of_cubic
  rw [cubic,←origin u B d]
  exact mul_ne_zero correction (pow_ne_zero 2 first)

theorem nonzero (u : Bool→K) (B : Bool→Bool→K) (d : K)
    (binaryOrigin : B false false≠0) (correction : d≠0) : value u B d≠0 := by
  intro zero
  have h0:=congrFun zero ![false,false,false]
  have h1:=congrFun zero ![true,false,false]
  have ht:=congrFun zero ![true,true,true]
  simp [value,funext_iff,Fin.forall_fin_succ] at h0 h1 ht
  have z0 : u false=0 := h0.resolve_right binaryOrigin
  have z1 : u true=0 := h1.resolve_right binaryOrigin
  exact correction (by simpa [z1] using ht)

theorem alternative (u : Bool→K) (B : Bool→Bool→K) (d : K)
    (binaryOrigin : B false false≠0) (correction : d≠0) :
    Prime (⟨3,value u B d⟩ : AnySignature K) ∨
      (value u B d≠0 ∧ value u B d (fun _=>false)=0) := by
  classical
  by_cases zero : value u B d (fun _=>false)=0
  · exact Or.inr ⟨nonzero u B d binaryOrigin correction,zero⟩
  · exact Or.inl (prime u B d zero correction)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryTernaryProductTop
end
