import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralZBinaryAlgebra

/-! The reciprocal diagonal cancels precisely the top-left Gram entry. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalFilterAlgebra
open Holant
variable {K : Type} [Field K]
def target (f : Signature K 2) := -(f ![false,false]/f ![false,true])^2
def filtered (f : Signature K 2) : Signature K 2 := fun x=>
  f ![x 0,false]*f ![x 1,false]+target f*f ![x 0,true]*f ![x 1,true]

theorem top (f : Signature K 2) (hb : f ![false,true]≠0) : filtered f ![false,false]=0 := by
  simp only [filtered,target,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  field_simp
  <;> ring

theorem cross (a b c d : K) (hb : b≠0) :
    a*c+(-(a/b)^2)*b*d=(a/b)*(b*c-a*d) := by
  field_simp
  <;> ring

theorem cross_nonzero (f : Signature K 2) (ha : f ![false,false]≠0) (hb : f ![false,true]≠0)
    (det : f ![false,false]*f ![true,true]≠f ![false,true]*f ![true,false]) :
    filtered f ![false,true]≠0 := by
  change f ![false,false]*f ![true,false]+(-(f ![false,false]/f ![false,true])^2)*
    f ![false,true]*f ![true,true]≠0
  rw [cross _ _ _ _ hb]
  exact mul_ne_zero (div_ne_zero ha hb) (sub_ne_zero.mpr det.symm)

theorem symmetric (f : Signature K 2) : filtered f ![true,false]=filtered f ![false,true] := by
  simp only [filtered,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  ring

theorem anti (f : Signature K 2) (hb : f ![false,true]≠0) (zero : filtered f ![true,true]=0) :
    filtered f=NoXWeightedAntiSigned.anti (filtered f ![false,true]) (filtered f ![false,true]) := by
  funext x
  have hx : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [hx]
  cases h0:x 0 <;> cases h1:x 1
  · exact top f hb
  · rfl
  · exact symmetric f
  · exact zero


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalFilterAlgebra
end
