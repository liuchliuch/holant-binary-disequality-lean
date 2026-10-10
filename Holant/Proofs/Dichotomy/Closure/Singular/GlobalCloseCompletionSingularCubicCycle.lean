import Holant.EightVertex.ProductAnchor.Source

/-! Four actual symmetric even cubic resources in a native-X cycle yield a
dense quaternary equality-anchor source. Every original port and scalar is
retained. The four-cycle coefficients are proved by the complete finite bit
expansion; no rank-one tensor or equality realization is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularCubicCycle
open Holant Holant.Tractable
open Holant.EightVertex.ProductAnchor
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
set_option maxRecDepth 16384
set_option Elab.async false

/-- The symmetric even row [A,0,B,0]. -/
def cubic (A B : Scalar) : Signature Scalar 3 := fun x=>
  if xor (xor (x 0) (x 1)) (x 2) then 0 else
    if x 0 || x 1 || x 2 then B else A

/-- Old consecutive cubic ports map to four paired cycle edges followed by
four external ports. Each cubic has external, next and previous ports. -/
def order : Equiv.Perm (Fin 12) where
  toFun := ![8,0,7,9,2,1,10,4,3,11,6,5]
  invFun := ![1,5,4,8,7,11,10,2,0,3,6,9]
  left_inv := by decide
  right_inv := by decide

def four (f : Signature Scalar 3) : Signature Scalar 12 :=
  Signature.tensor (Signature.tensor f f) (Signature.tensor f f)

theorem four_value (f : Signature Scalar 3) (z : Fin 12→Bool) :
    four f z = (f ![z 0,z 1,z 2] * f ![z 3,z 4,z 5]) *
      (f ![z 6,z 7,z 8] * f ![z 9,z 10,z 11]) := by
  simp only [four, Signature.tensor_apply]
  apply congrArg₂ (·*·)
  all_goals
    apply congrArg₂ (·*·)
    all_goals
      apply congrArg f
      funext i
      fin_cases i <;> rfl

theorem wired_value (f : Signature Scalar 3) (z : Fin 12→Bool) :
    Tensor.reindex order (four f) z =
      (f ![z 8,z 0,z 7] * f ![z 9,z 2,z 1]) *
      (f ![z 10,z 4,z 3] * f ![z 11,z 6,z 5]) := by
  simp only [four, Tensor.reindex_apply, Signature.tensor_apply]
  apply congrArg₂ (·*·)
  all_goals
    apply congrArg₂ (·*·)
    all_goals
      apply congrArg f
      funext i
      fin_cases i <;> rfl

def cycle (f : Signature Scalar 3) : Signature Scalar 4 :=
  Signature.contract Signature.disequality
    (Signature.contract Signature.disequality
      (Signature.contract Signature.disequality
        (Signature.contract Signature.disequality (Tensor.reindex order (four f)))))

theorem cycle_realizes (F : SignatureFamily Scalar) (f : Signature Scalar 3)
    (hf : Gadget.Realizes F .disequality f) : Gadget.RealizesUpTo F .disequality (cycle f) := by
  have two := OpenNetworkComposition.realizes_tensor F .disequality f f hf hf
  have fourR := OpenNetworkComposition.realizes_tensor F .disequality _ _ two two
  have wire := Dihedral.CompatibleClosure.realizes_reindex F .disequality
    (four f) fourR order.symm
  have first := OpenNetworkComposition.realizes_contract F _ wire (by norm_num)
  have second := OpenNetworkComposition.realizesUpTo_contract F _ first (by norm_num)
  have third := OpenNetworkComposition.realizesUpTo_contract F _ second (by norm_num)
  exact OpenNetworkComposition.realizesUpTo_contract F _ third (by norm_num)

private theorem value0000 (A B : Scalar) :
    cycle (cubic A B) ![false,false,false,false]=2*A^2*B^2 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value0001 (A B : Scalar) :
    cycle (cubic A B) ![false,false,false,true]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value0010 (A B : Scalar) :
    cycle (cubic A B) ![false,false,true,false]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value0011 (A B : Scalar) :
    cycle (cubic A B) ![false,false,true,true]=2*A*B^3 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value0100 (A B : Scalar) :
    cycle (cubic A B) ![false,true,false,false]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value0101 (A B : Scalar) :
    cycle (cubic A B) ![false,true,false,true]=2*A*B^3 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value0110 (A B : Scalar) :
    cycle (cubic A B) ![false,true,true,false]=2*A*B^3 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value0111 (A B : Scalar) :
    cycle (cubic A B) ![false,true,true,true]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1000 (A B : Scalar) :
    cycle (cubic A B) ![true,false,false,false]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1001 (A B : Scalar) :
    cycle (cubic A B) ![true,false,false,true]=2*A*B^3 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1010 (A B : Scalar) :
    cycle (cubic A B) ![true,false,true,false]=2*A*B^3 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1011 (A B : Scalar) :
    cycle (cubic A B) ![true,false,true,true]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1100 (A B : Scalar) :
    cycle (cubic A B) ![true,true,false,false]=2*A*B^3 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1101 (A B : Scalar) :
    cycle (cubic A B) ![true,true,false,true]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1110 (A B : Scalar) :
    cycle (cubic A B) ![true,true,true,false]=0 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

private theorem value1111 (A B : Scalar) :
    cycle (cubic A B) ![true,true,true,true]=2*B^4 := by
  simp only [cycle, Signature.contract_disequality, Tensor.reindex_apply]
  simp only [four_value]
  norm_num [order, cubic] <;> ring

theorem cycle_value (A B : Scalar) (x : Fin 4→Bool) :
    cycle (cubic A B) x =
      if weight x=0 then 2*A^2*B^2 else
      if weight x=2 then 2*A*B^3 else
      if weight x=4 then 2*B^4 else 0 := by
  have hx : x=![x 0,x 1,x 2,x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  generalize x 0=a, x 1=b, x 2=c, x 3=d
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [weight_four, value0000, value0001, value0010, value0011, value0100, value0101, value0110, value0111, value1000, value1001, value1010, value1011, value1100, value1101, value1110, value1111]


theorem cycle_dense (A B : Scalar) (hA : A≠0) (hB : B≠0) :
    DenseForm (cycle (cubic A B)) := by
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq ((B/A : Scalar) : ℂ) (by decide : 0<2)
  let r : Scalar := ⟨v,IsIntegral.of_pow (n:=2) (by decide) (by
    rw [hv]
    exact (B/A : Scalar).property)⟩
  have hr2 : r^2=B/A := Subtype.ext hv
  have hr : r≠0 := by
    intro zero
    exact (div_ne_zero hB hA) (by simpa [zero] using hr2.symm)
  have hr4 : r^4=(B/A)^2 := by
    calc r^4=(r^2)^2 := by ring
         _=(B/A)^2 := by rw [hr2]
  refine ⟨2*A^2*B^2,r,mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA))
    (pow_ne_zero _ hB),hr,(fun _=>false),?_⟩
  intro x
  rw [cycle_value]
  have hx : x=![x 0,x 1,x 2,x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  generalize x 0=a, x 1=b, x 2=c, x 3=d
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [weight_four, bitSign, hr2, hr4] <;>
    field_simp [hA] <;> ring

theorem scale_dense {q : Signature Scalar 4} (dense : DenseForm q)
    (c : Scalar) (hc : c≠0) : DenseForm (fun x=>c*q x) := by
  obtain ⟨rho,r,hrho,hr,s,he⟩ := dense
  refine ⟨c*rho,r,mul_ne_zero hc hrho,hr,s,?_⟩
  intro x
  change c*q x=_
  rw [he x]
  by_cases hx : weight x % 2=0
  · rw [if_pos hx,if_pos hx]
    ring
  · simp only [if_neg hx,mul_zero]

/-- The cycle is a genuine same-family construction. Possible nonzero
wire-circle multipliers are retained and absorbed into the dense coefficient. -/
theorem equality_anchor (F : SignatureFamily Scalar) (A B : Scalar)
    (hA : A≠0) (hB : B≠0)
    (actual : Gadget.Realizes F .disequality (cubic A B)) : HasEqualityAnchor F := by
  obtain ⟨c,hc,realized⟩ := cycle_realizes F (cubic A B) actual
  exact dense_realizing_family_anchor (fun x=>c*cycle (cubic A B) x)
    (scale_dense (cycle_dense A B hA hB) c hc) F realized


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularCubicCycle
end
