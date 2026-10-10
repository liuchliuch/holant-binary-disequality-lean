import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTernarySmallCubic
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryInteractionMatching
import Mathlib.Tactic.LinearCombination

/-! The quaternary binary-UPF base is an exact product of two binary blocks
plus one top coefficient. Cross interactions vanish by the actual matching
theorem; the small-cap cubic identities determine all four triple entries.
No tensor normal form is supplied by a classifier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryProductTop
open Holant
namespace C
export GlobalCloseCompletionUnaryTernarySmallCubic (cubic)
end C
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor double)
export GlobalCloseCompletionUnaryPinnedProduct (single)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option Elab.async false
variable {K : Type} [Field K]

def cap (f : Signature K 4) (i : Fin 4) : Signature K 3 :=
  fun x=>f (fun j=>(Fin.cons false x : Fin 4→Bool) ((Equiv.swap 0 i) j))

theorem cap0 (f : Signature K 4) : cap f 0=(fun x=>f ![false,x 0,x 1,x 2]) := by
  funext x
  unfold cap
  congr 1
  funext j
  fin_cases j <;>rfl
theorem cap1 (f : Signature K 4) : cap f 1=(fun x=>f ![x 0,false,x 1,x 2]) := by
  funext x
  unfold cap
  congr 1
  funext j
  fin_cases j <;>rfl
theorem cap2 (f : Signature K 4) : cap f 2=(fun x=>f ![x 1,x 0,false,x 2]) := by
  funext x
  unfold cap
  congr 1
  funext j
  fin_cases j <;>rfl
theorem cap3 (f : Signature K 4) : cap f 3=(fun x=>f ![x 2,x 0,x 1,false]) := by
  funext x
  unfold cap
  congr 1
  funext j
  fin_cases j <;>rfl

theorem complete_triple (q a b c p r s t : K) (hq : q≠0)
    (cubic : t*q^2-p*c*q-r*b*q-s*a*q+2*a*b*c=0)
    (first : r*q=a*c) (second : s*q=b*c) : t*q=p*c := by
  have h : (t*q-p*c)*q=0 := by linear_combination cubic+b*first+a*second
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hq)

theorem vector_value (f : Signature K 4) (x : Fin 4→Bool) : f x=f ![x 0,x 1,x 2,x 3] := by
  congr 1
  funext i
  fin_cases i <;>rfl

theorem minor_value (f : Signature K 4) (i j : Fin 4) : I.minor f i j=
    f ![false,false,false,false]*f ![I.double i j 0,I.double i j 1,I.double i j 2,I.double i j 3]-
      f ![I.single i 0,I.single i 1,I.single i 2,I.single i 3]*
        f ![I.single j 0,I.single j 1,I.single j 2,I.single j 3] := by
  unfold I.minor
  rw [vector_value f (fun _=>false),vector_value f (I.double i j),
    vector_value f (I.single i),vector_value f (I.single j)]

def product (f : Signature K 4) : Signature K 4 :=
  fun x=>f ![x 0,x 1,false,false]*f ![false,false,x 2,x 3]/f ![false,false,false,false]
def correction (f : Signature K 4) : K := f ![true,true,true,true]-product f ![true,true,true,true]

theorem reconstruct (f : Signature K 4) (origin : f ![false,false,false,false]≠0)
    (h02 : I.minor f 0 2=0) (h03 : I.minor f 0 3=0)
    (h12 : I.minor f 1 2=0) (h13 : I.minor f 1 3=0)
    (small : ∀i,C.cubic (cap f i)=0) :
    f=fun x=>product f x+if x=(fun _=>true) then correction f else 0 := by
  classical
  rw [minor_value] at h02 h03 h12 h13
  norm_num [I.double,I.single,Function.update] at h02 h03 h12 h13
  have c0:=small 0
  have c1:=small 1
  have c2:=small 2
  have c3:=small 3
  rw [cap0] at c0
  rw [cap1] at c1
  rw [cap2] at c2
  rw [cap3] at c3
  norm_num [C.cubic] at c0 c1 c2 c3
  have t0 : f ![false,true,true,true]*f ![false,false,false,false]=
      f ![false,false,true,true]*f ![false,true,false,false] := by
    apply complete_triple (f ![false,false,false,false]) (f ![false,false,true,false])
      (f ![false,false,false,true]) (f ![false,true,false,false]) (f ![false,false,true,true])
      (f ![false,true,true,false]) (f ![false,true,false,true]) (f ![false,true,true,true]) origin
    · linear_combination c0
    · linear_combination h12
    · linear_combination h13
  have t1 : f ![true,false,true,true]*f ![false,false,false,false]=
      f ![false,false,true,true]*f ![true,false,false,false] := by
    apply complete_triple (f ![false,false,false,false]) (f ![false,false,true,false])
      (f ![false,false,false,true]) (f ![true,false,false,false]) (f ![false,false,true,true])
      (f ![true,false,true,false]) (f ![true,false,false,true]) (f ![true,false,true,true]) origin
    · linear_combination c1
    · linear_combination h02
    · linear_combination h03
  have t2 : f ![true,true,false,true]*f ![false,false,false,false]=
      f ![true,true,false,false]*f ![false,false,false,true] := by
    apply complete_triple (f ![false,false,false,false]) (f ![true,false,false,false])
      (f ![false,true,false,false]) (f ![false,false,false,true]) (f ![true,true,false,false])
      (f ![true,false,false,true]) (f ![false,true,false,true]) (f ![true,true,false,true]) origin
    · linear_combination c2
    · linear_combination h03
    · linear_combination h13
  have t3 : f ![true,true,true,false]*f ![false,false,false,false]=
      f ![true,true,false,false]*f ![false,false,true,false] := by
    apply complete_triple (f ![false,false,false,false]) (f ![true,false,false,false])
      (f ![false,true,false,false]) (f ![false,false,true,false]) (f ![true,true,false,false])
      (f ![true,false,true,false]) (f ![false,true,true,false]) (f ![true,true,true,false]) origin
    · linear_combination c3
    · linear_combination h02
    · linear_combination h12
  funext x
  have hx : x=![x 0,x 1,x 2,x 3] := by funext i;fin_cases i <;>rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp only [product,correction,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      funext_iff,Fin.forall_fin_succ] <;> norm_num
  all_goals field_simp [origin]
  all_goals first
    | solve | linear_combination h02
    | solve | linear_combination h03
    | solve | linear_combination h12
    | solve | linear_combination h13
    | solve | linear_combination t0
    | solve | linear_combination t1
    | solve | linear_combination t2
    | solve | linear_combination t3
    | solve | ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryProductTop
end
