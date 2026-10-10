import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternaryForm

/-! Both literal Boolean caps eliminate every singleton in the quaternary
product-plus-top form. The surviving source has paired support and a genuine
nonzero compressed determinant, derived from primality and the cap equations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinQuaternary
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace C
export GlobalCloseCompletionUnaryTernarySmallCubic (cubic)
end C
namespace Q
export GlobalCloseCompletionUnaryQuaternaryProductTop (product correction reconstruct)
end Q
namespace F
export GlobalCloseCompletionUnaryQuaternaryForm (left right Paired determinant paired nonsingular correction_nonzero)
end F
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor)
export GlobalCloseCompletionUnaryPinnedProduct (single)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def cap (b : Bool) (f : Signature K 4) (i : Fin 4) : Signature K 3 :=
  fun x=>f (fun j=>(Fin.cons b x : Fin 4→Bool) ((Equiv.swap 0 i) j))

def productTop (A B : Bool→Bool→K) (d : K) : Signature K 4 :=
  fun x=>A (x 0) (x 1)*B (x 2) (x 3)+(if x=(fun _=>true) then d else 0)

theorem one_cap_cubic (A B : Bool→Bool→K) (d : K) (i : Fin 4) :
    C.cubic (cap true (productTop A B d) i)=
      d*(cap true (productTop A B d) i ![false,false,false])^2 := by
  fin_cases i <;>
    norm_num [C.cubic,cap,productTop,funext_iff,Fin.forall_fin_succ,Equiv.swap_apply_def] <;> ring

theorem one_cap_origin (f : Signature K 4) (i : Fin 4) :
    cap true f i ![false,false,false]=f (I.single i) := by
  apply congrArg f
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem form (f : Signature K 4)
    (reconstructed : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0) :
    f=productTop (F.left f) (F.right f) (Q.correction f) := by
  funext x
  rw [congrFun reconstructed x]
  simp only [productTop,F.left,F.right,Q.product,div_eq_mul_inv]
  ring

theorem singleton_zero (f : Signature K 4) (prime : Prime (⟨4,f⟩ : AnySignature K))
    (reconstructed : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0)
    (ones : ∀i,C.cubic (cap true f i)=0) : ∀i,f (I.single i)=0 := by
  have nonzero := F.correction_nonzero f prime reconstructed
  have equation := form f reconstructed
  intro i
  have identity := one_cap_cubic (F.left f) (F.right f) (Q.correction f) i
  have caps := congrArg (fun g : Signature K 4=>cap true g i) equation
  rw [←caps,ones i,one_cap_origin] at identity
  have square : f (I.single i)^2=0 := (mul_eq_zero.mp identity.symm).resolve_left nonzero
  by_contra live
  exact (pow_ne_zero 2 live) square

theorem paired_nonsingular (f : Signature K 4) (prime : Prime (⟨4,f⟩ : AnySignature K))
    (origin : f ![false,false,false,false]≠0)
    (h02 : I.minor f 0 2=0) (h03 : I.minor f 0 3=0)
    (h12 : I.minor f 1 2=0) (h13 : I.minor f 1 3=0)
    (caps : ∀i b,C.cubic (cap b f i)=0) : F.Paired f ∧ F.determinant f≠0 := by
  have reconstructed := Q.reconstruct f origin h02 h03 h12 h13 (fun i=>caps i false)
  exact ⟨F.paired f reconstructed (singleton_zero f prime reconstructed (fun i=>caps i true)),
    F.nonsingular f origin prime reconstructed⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinQuaternary
end
