import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.SelfLoop
import Holant.Proofs.Hardness.LabelledNetwork

/-!
# Thin local pin-normalized ONE/TWO networks over the original coefficient field

This separates the literal network arithmetic from any UA/PureStep/Ready or
whole-family continuation. Network constructors and port permutations are the
same as the existing WeightedSixVertex/WeightedBinary/WeightedNativeUnitGadgets
local constructions. The thin definitions are generic in the original tensor M
and coefficient field; no coefficient normalization, unary-access theorem or
source-produced success packet is an input.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitLocal
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.Certificates.FourthRootOdd
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains
  (tensor tensor_denote reindex reindex_denote binarySignature)
end Chain
variable {K : Type*} [Field K]

def pin (b : Bool) : Signature K 1 := fun x => if x 0=b then 1 else 0

def pinPorts (one : Bool) : Equiv.Perm (Fin 5) where
  toFun := if one then ![0,2,3,4,1] else ![2,3,0,4,1]
  invFun := if one then ![0,4,1,2,3] else ![2,4,0,1,3]
  left_inv := by intro i; cases one <;> fin_cases i <;> rfl
  right_inv := by intro i; cases one <;> fin_cases i <;> rfl

def pinned (one : Bool) (N : Network K 4) : Network K 3 :=
  (reorderNetwork (N.tensor (Network.corolla (pin (!one)))) (pinPorts one)).contract Signature.disequality

theorem pinned_value (one : Bool) (N : Network K 4) (x : Fin 3 → Bool) :
    (pinned one N).denote x=
      if one then N.denote ![true,x 0,x 1,x 2] else N.denote ![x 0,x 1,false,x 2] := by
  rw [pinned,Network.denote_contract,reorderNetwork_denote,Network.denote_tensor,
    Network.denote_corolla,Signature.contract_disequality]
  have hq (a b : Bool) :
      (fun i : Fin 4 => (Fin.cons a (Fin.cons b x) : Fin 5 → Bool) ((pinPorts one) (Fin.castAdd 1 i)))=
        if one then ![a,x 0,x 1,x 2] else ![x 0,x 1,a,x 2] := by
    cases one <;> funext i <;> fin_cases i <;> rfl
  have hp (a b : Bool) :
      (fun i : Fin 1 => (Fin.cons a (Fin.cons b x) : Fin 5 → Bool) ((pinPorts one) (Fin.natAdd 4 i)))=fun _ => b := by
    cases one <;> funext i <;> fin_cases i <;> rfl
  simp only [Tensor.reindex_apply,Signature.tensor_apply,hq,hp]
  cases one <;> simp [pin]

def weights (M : Signature K 4) (one : Bool) : Fin 3 → K :=
  if one then ![(entries M).a*(entries M).x,(entries M).d*(entries M).z,(entries M).c*(entries M).z]
    else ![(entries M).c*(entries M).d,(entries M).c*(entries M).z,(entries M).a*(entries M).x]

def weighted (one : Bool) (w : Fin 3 → K) : Signature K 3 := fun x =>
  if one then match x 0,x 1,x 2 with
    | true,false,false => w 0
    | false,true,false => w 1
    | false,false,true => w 2
    | _,_,_ => 0
  else match x 0,x 1,x 2 with
    | false,true,true => w 0
    | true,false,true => w 1
    | true,true,false => w 2
    | _,_,_ => 0

def cube (M : Signature K 4) (one : Bool) : Network K 3 := pinned one (nativeChain M)

theorem cube_value (M : Signature K 4) (hM : EvenSupport M) (hs : SparseCase M) (one : Bool) :
    (cube M one).denote=weighted one (weights M one) := by
  funext x
  rw [cube,pinned_value,nativeChain_sparse M hM hs]
  cases one <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [weighted,weights,table,sparseEntries,h0,h1,h2]

theorem weights_nonzero (M : Signature K 4) (hs : SparseCase M) (hc : NonzeroCorners M)
    (one : Bool) (i : Fin 3) : weights M one i≠0 := by
  rcases hs with ⟨_hb,_hy,_hw,hc',hd,hz⟩
  cases one <;> fin_cases i
  all_goals simp only [weights,if_true,if_false,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals first | exact hc | exact mul_ne_zero hc' hd | exact mul_ne_zero hc' hz | exact mul_ne_zero hd hz

def pinOrder : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide
  right_inv := by decide

def pinNetwork (one : Bool) (N : Network K 3) : Network K 2 :=
  (Chain.reindex (Chain.tensor N (Network.corolla (pin one))) pinOrder).contract Signature.disequality

theorem pinNetwork_value (one : Bool) (N : Network K 3) (x : Fin 2 → Bool) :
    (pinNetwork one N).denote x=if one then N.denote ![false,x 0,x 1] else N.denote ![true,x 0,x 1] := by
  rw [pinNetwork,Network.denote_contract,Chain.reindex_denote,Chain.tensor_denote,
    Network.denote_corolla,Signature.contract_disequality]
  have hc (a b : Bool) :
      (fun i : Fin 3 => (Fin.cons a (Fin.cons b x) : Fin 4 → Bool) (pinOrder (Fin.castAdd 1 i)))=![a,x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  have hp (a b : Bool) :
      (fun i : Fin 1 => (Fin.cons a (Fin.cons b x) : Fin 4 → Bool) (pinOrder (Fin.natAdd 3 i)))=fun _ => b := by
    funext i
    fin_cases i <;> rfl
  simp only [Tensor.reindex_apply,Signature.tensor_apply,hc,hp]
  cases one <;> simp [pin]

def binary (M : Signature K 4) (one : Bool) : Network K 2 := pinNetwork one (cube M one)

theorem binary_value (M : Signature K 4) (hM : EvenSupport M) (hs : SparseCase M) (one : Bool) :
    (binary M one).denote=Chain.binarySignature (weightedX
      (if one then weights M one 2 else weights M one 1)
      (if one then weights M one 1 else weights M one 2)) := by
  funext x
  rw [binary,pinNetwork_value,cube_value M hM hs]
  cases one <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [weighted,Chain.binarySignature,weightedX,h0,h1]

def tailOrder : Equiv.Perm (Fin 3) where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv := by decide
  right_inv := by decide

def third (M : Signature K 4) : Network K 2 :=
  pinNetwork false (Chain.reindex (cube M false) tailOrder)

theorem third_value (M : Signature K 4) (hM : EvenSupport M) (hs : SparseCase M) :
    (third M).denote=Chain.binarySignature (weightedX (weights M false 0) (weights M false 1)) := by
  funext x
  rw [third,pinNetwork_value,Chain.reindex_denote,cube_value M hM hs]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [weighted,Chain.binarySignature,weightedX,Tensor.reindex_apply,tailOrder,h0,h1]

def attachOrder (i : Fin 3) : Equiv.Perm (Fin 5) where
  toFun := if i=0 then ![0,3,4,1,2] else if i=1 then ![2,0,4,1,3] else ![2,3,0,1,4]
  invFun := if i=0 then ![0,3,4,1,2] else if i=1 then ![1,3,0,4,2] else ![2,3,0,1,4]
  left_inv := by intro p; fin_cases i <;> fin_cases p <;> rfl
  right_inv := by intro p; fin_cases i <;> fin_cases p <;> rfl

def attach (N : Network K 3) (B : Network K 2) (i : Fin 3) : Network K 3 :=
  (Chain.reindex (Chain.tensor N B) (attachOrder i)).contract Signature.disequality

theorem attach_sum (N : Network K 3) (B : Network K 2) (i : Fin 3) (x : Fin 3 → Bool) :
    (attach N B i).denote x=
      ∑a : Bool,∑b : Bool,Signature.disequality a b*(N.denote (Function.update x i a)*B.denote ![b,x i]) := by
  rw [attach,Network.denote_contract,Chain.reindex_denote,Chain.tensor_denote]
  have hc (a b : Bool) :
      (fun p : Fin 3 => (Fin.cons a (Fin.cons b x) : Fin 5 → Bool) ((attachOrder i) (Fin.castAdd 2 p)))=Function.update x i a := by
    fin_cases i <;> funext p <;> fin_cases p <;> simp [attachOrder,Function.update] <;> rfl
  have hb (a b : Bool) :
      (fun p : Fin 2 => (Fin.cons a (Fin.cons b x) : Fin 5 → Bool) ((attachOrder i) (Fin.natAdd 3 p)))=![b,x i] := by
    fin_cases i <;> funext p <;> fin_cases p <;> rfl
  simp only [Signature.contract,Tensor.reindex_apply,Signature.tensor_apply,hc,hb]

theorem attach_anti (N : Network K 3) (B : Network K 2) (i : Fin 3) (u v : K)
    (hB : B.denote=Chain.binarySignature (weightedX u v)) (x : Fin 3 → Bool) :
    (attach N B i).denote x=N.denote x*(if x i then u else v) := by
  rw [attach_sum]
  have he : Function.update x i (x i)=x := by rw [Function.update_eq_self]
  cases hx : x i
  · have hu : Function.update x i false=x := by simpa only [hx] using he
    simp [hB,Chain.binarySignature,weightedX,Signature.disequality,hx,hu]
  · have hu : Function.update x i true=x := by simpa only [hx] using he
    simp [hB,Chain.binarySignature,weightedX,Signature.disequality,hx,hu]

def swapOrder : Equiv.Perm (Fin 2) where
  toFun := ![1,0]
  invFun := ![1,0]
  left_inv := by decide
  right_inv := by decide

def swap (B : Network K 2) : Network K 2 := Chain.reindex B swapOrder

theorem swap_anti (B : Network K 2) (u v : K)
    (hB : B.denote=Chain.binarySignature (weightedX u v)) :
    (swap B).denote=Chain.binarySignature (weightedX v u) := by
  funext x
  rw [swap,Chain.reindex_denote,hB]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Chain.binarySignature,weightedX,Tensor.reindex_apply,swapOrder,h0,h1]

def unitNetwork (M : Signature K 4) (one : Bool) : Network K 3 :=
  if one then attach (attach (cube M true) (binary M false) 0) (binary M true) 1
  else attach (attach (cube M false) (third M) 0) (swap (binary M false)) 2

def scale (M : Signature K 4) (one : Bool) : K :=
  (weights M one 0*weights M one 1)*weights M one 2

def ONE : Signature K 3 := fun x =>
  if ((if x 0 then 1 else 0)+(if x 1 then 1 else 0)+(if x 2 then 1 else 0) : ℕ)==1 then 1 else 0

def TWO : Signature K 3 := fun x => ONE (fun i => !x i)
def unit (one : Bool) : Signature K 3 := if one then ONE else TWO

/-- Full eight-coefficient equality of the actual original-M network. -/
theorem unit_value (M : Signature K 4) (hM : EvenSupport M) (hs : SparseCase M) (one : Bool) :
    (unitNetwork M one).denote=scale M one • unit one := by
  have hOne := binary_value M hM hs true
  have hTwo := binary_value M hM hs false
  have hThird := third_value M hM hs
  have hSwap := swap_anti _ _ _ hTwo
  cases one
  · funext x
    simp only [unitNetwork,Bool.false_eq_true,if_false]
    rw [attach_anti _ _ 2 _ _ hSwap,attach_anti _ _ 0 _ _ hThird,cube_value M hM hs false]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp [unit,scale,weights,weighted,ONE,TWO,Pi.smul_apply,smul_eq_mul,h0,h1,h2] <;> first | trivial | ring
    all_goals simp
  · funext x
    simp only [unitNetwork,if_true]
    rw [attach_anti _ _ 1 _ _ hOne,attach_anti _ _ 0 _ _ hTwo,cube_value M hM hs true]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp [unit,scale,weights,weighted,ONE,Pi.smul_apply,smul_eq_mul,h0,h1,h2] <;> first | trivial | ring
    all_goals simp

theorem scale_nonzero (M : Signature K 4) (hs : SparseCase M) (hc : NonzeroCorners M) (one : Bool) :
    scale M one≠0 :=
  mul_ne_zero (mul_ne_zero (weights_nonzero M hs hc one 0) (weights_nonzero M hs hc one 1))
    (weights_nonzero M hs hc one 2)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitLocal
