import Holant.Proofs.CountingMachines.CircuitNative.GateAlphabet
import Holant.Proofs.CountingMachines.CircuitNative.CircuitSemantics

/-! Literal signed independent-set factors for the accepted Boolean circuit
alphabet. The only binary constraint is NAND2; the only auxiliary unary is
[1,-1]. Each eliminated gadget has scalar one. This is finite semantics, not
an assumed availability of the signed unary in the final oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportGates
open Holant
open Holant.LocalDrafts.RemoteWork.CountingBridge
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommRing K]

def nand (x y : Bool) : K := if x && y then 0 else 1
def sign (x : Bool) : K := if x then -1 else 1
def implication (x y : Bool) : K := if x && !y then 0 else 1

private theorem cons_three_last (a b c : Bool) (z : Fin 0→Bool) :
    (Fin.cons a (Fin.cons b (Fin.cons c z)) : Fin 3→Bool) 2=c := rfl

/-- A negative clause vertex is forbidden from selection exactly when at
least one adjacent literal is selected. -/
def clause {n : ℕ} (x : Fin n→Bool) (z : Bool) : K :=
  sign z * ∏i,nand z (x i)

theorem clause_sum {n : ℕ} (x : Fin n→Bool) :
    (∑z : Bool,clause (K:=K) x z)=if ∃i,x i=true then 1 else 0 := by
  classical
  simp only [clause,Fintype.sum_bool,sign,Bool.false_eq_true,ite_false,ite_true,
    nand,Bool.false_and,Bool.true_and,one_mul,neg_one_mul]
  by_cases h : ∃i,x i=true
  · obtain ⟨i,hi⟩ := h
    rw [ite_eq_left ⟨i,hi⟩]
    have hz : (∏j,if x j then (0 : K) else 1)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [hz]
  · rw [ite_eq_right h]
    have hx : ∀i,x i=false := by
      intro i
      cases hh : x i
      · rfl
      · exact False.elim (h ⟨i,hh⟩)
    simp [hx]

def different (x y z : Bool) : K := nand x y * clause ![x,y] z

/-- NAND excludes (1,1), the signed common neighbor excludes (0,0), and
both surviving rails carry coefficient one. -/
theorem different_sum (x y : Bool) :
    (∑z : Bool,different (K:=K) x y z)=if y=(!x) then 1 else 0 := by
  simp only [different,←Finset.mul_sum,clause_sum]
  cases x <;> cases y <;> norm_num [nand,Fin.exists_fin_succ]

/-- The implication three-support relation also generates NAND2 with one
signed auxiliary vertex. The original orientation is retained. -/
theorem implication_nand (x y : Bool) :
    (∑z : Bool,sign (K:=K) z * implication z x * implication z y)=nand x y := by
  cases x <;> cases y <;> simp [Fintype.sum_bool,sign,implication,nand]

/-- Nine actual internal Boolean choices: three complement rails, three
signed rail-clause vertices, and three signed NAND-clause vertices. -/
def nandGateWeight (x y o : Bool) (r : Fin 3→Bool) (s : Fin 3→Bool)
    (t : Fin 3→Bool) : K :=
  different x (r 0) (s 0) * different y (r 1) (s 1) *
    different o (r 2) (s 2) *
    clause ![x,o] (t 0) * clause ![y,o] (t 1) *
    clause ![r 0,r 1,r 2] (t 2)

theorem sum_three (f g h : Bool→K) :
    (∑z : Fin 3→Bool,f (z 0)*g (z 1)*h (z 2))=
      (∑x : Bool,f x)*(∑y : Bool,g y)*(∑o : Bool,h o) := by
  simp only [CircuitSemantics.sum_cons,Fintype.sum_unique,Fintype.sum_bool,
    Fin.cons_zero,Fin.cons_one,Fin.cons_succ,Fin.isValue]
  change (f true*g true*h true+f true*g true*h false+
    (f true*g false*h true+f true*g false*h false))+
    (f false*g true*h true+f false*g true*h false+
      (f false*g false*h true+f false*g false*h false))=_
  ring

theorem nandGate_sum (x y o : Bool) :
    (∑r : Fin 3→Bool,∑s : Fin 3→Bool,∑t : Fin 3→Bool,
      nandGateWeight (K:=K) x y o r s t)=Gates.nand ![x,y,o] := by
  have hclause (r : Fin 3→Bool) :
      (∑t : Fin 3→Bool,clause (K:=K) ![x,o] (t 0) *
        clause ![y,o] (t 1) * clause ![r 0,r 1,r 2] (t 2))=
      (if x || o then (1 : K) else 0)*(if y || o then 1 else 0)*
        (if r 0 || r 1 || r 2 then 1 else 0) := by
    rw [sum_three]
    simp only [clause_sum,Fin.exists_fin_succ,Fin.isValue]
    cases x <;> cases y <;> cases o <;> cases r 0 <;> cases r 1 <;> cases r 2 <;> simp
  have ht (r s : Fin 3→Bool) :
      (∑t : Fin 3→Bool,nandGateWeight (K:=K) x y o r s t)=
      (different x (r 0) (s 0)*different y (r 1) (s 1)*different o (r 2) (s 2))*
        ((if x || o then (1 : K) else 0)*(if y || o then 1 else 0)*
          (if r 0 || r 1 || r 2 then 1 else 0)) := by
    rw [←hclause,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    unfold nandGateWeight
    ring
  simp_rw [ht,←Finset.sum_mul,sum_three,different_sum]
  simp only [CircuitSemantics.sum_cons,Fintype.sum_unique,Fintype.sum_bool,
    Fin.cons_zero,Fin.cons_one,Fin.cons_succ,Fin.isValue]
  cases x <;> cases y <;> cases o <;>
    norm_num [Gates.nand,cons_three_last]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportGates
