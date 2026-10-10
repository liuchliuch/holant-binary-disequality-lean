import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedPortsIncidence
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniform

/-! Literal signed substitution through a full weighted antidiagonal. Every
private weight is retained as an explicit product on the exposed variables.
Equal fourth powers make that product an invertible Affine multiplier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedSignedPorts
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSignedPortsCore (Port word arity external privatePort rowPorts pinNode
  privateRows fixedRows recipe privateAssignment original_word pin)
open scoped BigOperators
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue (coefficient)
end B
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace A
export NoXWeightedAntiSigned (anti)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m : ℕ} {K : Type} [Field K]

def table (f : Signature K n) (v w : K) (j : Fin 4) : Signature K (arity n j.val) :=
  match j with
  | ⟨0,_⟩=>f
  | ⟨1,_⟩=>A.anti v w
  | ⟨2,_⟩=>pin false
  | ⟨3,_⟩=>pin true
  | ⟨j+4,h⟩=>False.elim (by omega)

def rowValue (f : Signature K n) (v w : K)
    (node : Node (u:=1) (s:=4) (a:=fun _=>m+n) (b:=arity n) 0)
    (bits : Fin (m+n)→Bool) : K := table f v w node.1 (T.substitute node.2 bits)

theorem pinNode_value (f : Signature K n) (v w : K) (bit : Bool) (p : Bool ⊕ Fin (m+n))
    (bits : Fin (m+n)→Bool) :
    rowValue f v w (pinNode bit p) bits=if Sum.elim id bits p=bit then 1 else 0 := by
  cases bit <;> cases p <;> rfl

def privateFactor (v w : K) (p : Fin n→Port m) (bits : Fin (m+n)→Bool) (i : Fin n) : K :=
  match p i with
  | .inr (j,true)=>A.anti v w ![bits (privatePort i),bits (external j)]
  | _=>(if bits (privatePort i)=false then 1 else 0)^2

def portWeight (v w : K) (p : Port m) (z : Fin m→Bool) : K :=
  match p with
  | .inr (j,true)=>if z j then v else w
  | _=>1

def weight (v w : K) (p : Fin n→Port m) (z : Fin m→Bool) : K := ∏i,portWeight v w (p i) z

theorem coefficient_value (f : Signature K n) (v w : K) (p : Fin n→Port m) (bits : Fin (m+n)→Bool) :
    coefficient (table f v w) (recipe p) 0 bits=
      f (T.substitute (rowPorts p) bits)*∏i,privateFactor v w p bits i := by
  simp only [coefficient,B.coefficient,recipe,List.map_append,List.prod_append,
    List.map_cons,List.prod_cons,List.map_flatten,List.prod_flatten,List.map_ofFn,List.prod_ofFn]
  change (f (T.substitute (rowPorts p) bits)*
    ∏i,((privateRows p i).map (fun node=>rowValue f v w node bits)).prod)*
    (∏i,((fixedRows p i).map (fun node=>rowValue f v w node bits)).prod)=_
  have hp (i : Fin n) : ((privateRows p i).map (fun node=>rowValue f v w node bits)).prod=
      privateFactor v w p bits i := by
    cases h : p i with
    | inl bit=>cases hb : bits (privatePort i) <;>
        simp [privateRows,privateFactor,h,rowValue,table,pinNode,pin,T.substitute,pow_two,hb]
    | inr pair=>
        rcases pair with ⟨j,sgn⟩
        cases sgn <;> cases hb : bits (privatePort i) <;>
          simp [privateRows,privateFactor,h,rowValue,table,pinNode,pin,T.substitute,pow_two,hb,A.anti]
  have hf (i : Fin n) : ((fixedRows p i).map (fun node=>rowValue f v w node bits)).prod=1 := by
    cases h : p i with
    | inl bit=>
        simp only [fixedRows,h,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,pinNode_value]
        simp
    | inr pair=>simp [fixedRows,h]
  simp_rw [hp,hf]
  simp

theorem private_factor (v w : K) (p : Fin n→Port m) (z : Fin m→Bool) (y : Fin n→Bool) (i : Fin n) :
    privateFactor v w p (Fin.addCases z y) i=
      portWeight v w (p i) z*(if y i=privateAssignment p z i then 1 else 0) := by
  cases h : p i with
  | inl bit=>cases hy : y i <;> simp [privateFactor,portWeight,privateAssignment,h,privatePort,hy]
  | inr pair=>
      rcases pair with ⟨j,sgn⟩
      cases sgn <;> cases hy : y i <;> cases hz : z j <;>
        simp [privateFactor,portWeight,privateAssignment,h,privatePort,external,A.anti,hy,hz]

def trace (f : Signature K n) (v w : K) (p : Fin n→Port m) : Signature K m := fun z=>
  ∑y : Fin n→Bool,coefficient (table f v w) (recipe p) 0 (Fin.addCases z y)

theorem trace_value (f : Signature K n) (v w : K) (p : Fin n→Port m) (z : Fin m→Bool) :
    trace f v w p z=weight v w p z*f (word p z) := by
  classical
  unfold trace
  simp_rw [coefficient_value,private_factor,Finset.prod_mul_distrib]
  have prod (y : Fin n→Bool) :
      (∏i,if y i=privateAssignment p z i then (1:K) else 0)=
        if y=privateAssignment p z then 1 else 0 := by
    rw [Fintype.prod_boole]
    simp only [funext_iff]
    by_cases he : ∀i,y i=privateAssignment p z i <;> simp [he]
  simp_rw [prod]
  rw [Finset.sum_eq_single (privateAssignment p z)]
  · rw [ite_eq_left rfl,mul_one,original_word]
    exact mul_comm _ _
  · intro y _ hy
    simp [hy]
  · simp

section Phase
variable (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0)

include hv hw in
theorem portWeight_ne_zero (p : Port m) (z : Fin m→Bool) : portWeight v w p z≠0 := by
  cases p with
  | inl bit=>exact one_ne_zero
  | inr pair=>
      rcases pair with ⟨j,sgn⟩
      cases sgn
      · exact one_ne_zero
      · cases hz : z j
        · simpa [portWeight,hz] using hw
        · simpa [portWeight,hz] using hv

include hv hw in
theorem weight_ne_zero (p : Fin n→Port m) (z : Fin m→Bool) : weight v w p z≠0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>portWeight_ne_zero v w hv hw (p i) z)

variable (fourth : v^4=w^4)
include hw fourth in
theorem portWeight_affine (p : Port m) : Affine (portWeight v w p) := by
  cases p with
  | inl bit=>exact affine_constant m 1
  | inr pair=>
      rcases pair with ⟨j,sgn⟩
      cases sgn
      · exact affine_constant m 1
      · exact GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers j w v hw fourth.symm

include hw fourth in
theorem weight_affine (p : Fin n→Port m) : Affine (weight v w p) :=
  OrdinaryNegativeSignedRowsUniform.affine_prod Finset.univ
    (fun i=>portWeight v w (p i)) (fun i _=>portWeight_affine v w hw fourth (p i))

include hv hw fourth in
theorem weight_affine_iff (p : Fin n→Port m) (f : Signature AlgebraicComplex m) :
    Affine (fun z=>weight v w p z*f z) ↔ Affine f := by
  constructor
  · intro h
    have inverse := OrdinaryNegativeAffineSquareReciprocal.affine_inverse _ (weight_affine v w hw fourth p)
    convert inverse.mul h using 1
    funext z
    rw [←mul_assoc,inv_mul_cancel₀ (weight_ne_zero v w hv hw p z),one_mul]
  · exact (weight_affine v w hw fourth p).mul
end Phase


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedSignedPorts
end
