import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneIncidence
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! The actual rank-one two-word restriction with a weighted antidiagonal
in place of literal X. Every phase factor is retained, and all old incidence
proofs apply because the physical port lists are identical. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankOneCore
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue (coefficient)
end B
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
open OrdinaryNegativeRankOneCore (arity external privatePort neg rowPorts pinNode privateRows fixedRows recipe
  privateAssignment original_word)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ}

variable {K : Type} [Field K]
def pin (b : Bool) : Signature K 1 := fun x=>if x 0=b then 1 else 0

def table (f : Signature K n) (v w : K) (j : Fin 4) : Signature K (arity n j.val) :=
  match j with
  | ⟨0,_⟩=>f
  | ⟨1,_⟩=>NoXWeightedAntiSigned.anti v w
  | ⟨2,_⟩=>pin false
  | ⟨3,_⟩=>pin true
  | ⟨j+4,h⟩=>False.elim (by omega)

def rowValue (f : Signature K n) (v w : K)
    (node : Node (u:=1) (s:=4) (a:=fun _=>1+n) (b:=arity n) 0)
    (bits : Fin (1+n)→Bool) : K := table f v w node.1 (T.substitute node.2 bits)

theorem pinNode_value (f : Signature K n) (v w : K) (b : Bool) (p : Bool ⊕ Fin (1+n))
    (bits : Fin (1+n)→Bool) :
    rowValue f v w (pinNode b p) bits=if Sum.elim id bits p=b then 1 else 0 := by
  cases b <;> cases p <;> rfl

theorem coefficient_value (f : Signature K n) (v w : K) (s t : Fin n→Bool) (bits : Fin (1+n)→Bool) :
    coefficient (table f v w) (recipe s t) 0 bits=
      f (T.substitute (rowPorts s t) bits)*
        ∏i,if neg s t i then NoXWeightedAntiSigned.anti v w ![bits (privatePort i),bits external]
          else (if bits (privatePort i)=false then 1 else 0)^2 := by
  simp only [coefficient,B.coefficient,recipe,List.map_append,List.prod_append,
    List.map_cons,List.prod_cons,List.map_flatten,List.prod_flatten,
    List.map_ofFn,List.prod_ofFn]
  change (f (T.substitute (rowPorts s t) bits)*
    ∏i,((privateRows s t i).map (fun node=>rowValue f v w node bits)).prod)*
    (∏i,((fixedRows s t i).map (fun node=>rowValue f v w node bits)).prod)=_
  have hp (i : Fin n) : ((privateRows s t i).map (fun node=>rowValue f v w node bits)).prod=
      if neg s t i then NoXWeightedAntiSigned.anti v w ![bits (privatePort i),bits external]
      else (if bits (privatePort i)=false then 1 else 0)^2 := by
    cases h : neg s t i <;> cases hw : bits (privatePort i) <;>
      simp [privateRows,h,rowValue,table,pinNode,pin,T.substitute,pow_two,hw,NoXWeightedAntiSigned.anti]
  have hf (i : Fin n) : ((fixedRows s t i).map (fun node=>rowValue f v w node bits)).prod=1 := by
    by_cases h : s i=t i
    · simp only [fixedRows,ite_eq_left h,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,pinNode_value]
      simp
    · simp [fixedRows,h]
  simp_rw [hp,hf]
  simp


def negativeCount (s t : Fin n→Bool) : ℕ := ∑i,if neg s t i then 1 else 0

theorem private_factor (s t : Fin n→Bool) (v w : K) (z : Fin 1→Bool) (y : Fin n→Bool) (i : Fin n) :
    (if neg s t i then NoXWeightedAntiSigned.anti v w
        ![Fin.addCases z y (privatePort i),Fin.addCases z y external]
      else (if Fin.addCases z y (privatePort i)=false then 1 else 0)^2)=
    (if neg s t i then (if z 0 then v else w) else 1)*
      (if y i=privateAssignment s t (z 0) i then 1 else 0) := by
  simp only [privatePort,external,Fin.addCases_left,Fin.addCases_right,privateAssignment]
  by_cases hn : neg s t i=true <;> cases y i <;> cases z 0 <;>
    simp [NoXWeightedAntiSigned.anti,hn]

theorem factor_product (s t : Fin n→Bool) (c : K) :
    (∏i,if neg s t i then c else 1)=c^negativeCount s t := by
  rw [negativeCount,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases neg s t i <;> simp

def trace (f : Signature K n) (v w : K) (s t : Fin n→Bool) : Signature K 1 := fun z=>
  ∑y : Fin n→Bool,coefficient (table f v w) (recipe s t) 0 (Fin.addCases z y)

/-- The one surviving assignment has the original coefficient multiplied
by its exact antidiagonal factor, rather than an asserted free X value. -/
theorem trace_value (f : Signature K n) (v w : K) (s t : Fin n→Bool) (z : Fin 1→Bool) :
    trace f v w s t z=(if z 0 then v else w)^negativeCount s t*(if z 0 then f t else f s) := by
  classical
  unfold trace
  simp_rw [coefficient_value,private_factor,Finset.prod_mul_distrib,factor_product]
  have prod (y : Fin n→Bool) :
      (∏i,if y i=privateAssignment s t (z 0) i then (1:K) else 0)=
        if y=privateAssignment s t (z 0) then 1 else 0 := by
    rw [Fintype.prod_boole]
    simp only [funext_iff]
    by_cases he : ∀i,y i=privateAssignment s t (z 0) i <;> simp [he]
  simp_rw [prod]
  rw [Finset.sum_eq_single (privateAssignment s t (z 0))]
  · rw [ite_eq_left rfl,mul_one,original_word]
    cases z 0 <;> simp [mul_comm]
  · intro y _ hy
    simp [hy]
  · simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankOneCore
end
