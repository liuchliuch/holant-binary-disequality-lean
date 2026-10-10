import Holant.Proofs.Hardness.BinaryThreeSupportGraph
import Holant.Proofs.Hardness.BinaryThreeSupportFilter
import Holant.Proofs.Hardness.BinaryCSPProgrammeRepeat
import Holant.Proofs.Hardness.BinaryCSPProgrammeValue

/-! The finite arbitrary-weight removal identity applied to the exact raw
unsigned graphs and positive-repetition writer used by the machine layer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportWeights
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace R
export BinaryThreeSupportGraph (Raw extend rowsWeight value)
end R
namespace G
export BinaryThreeSupportGates (nand)
end G
namespace F
export BinaryThreeSupportFilter (cubeRoots denominator count_constraints)
end F
namespace D
export ThreeModeAnnihilator (differenceFilter)
end D
namespace P
export BinaryCSPProgrammeRepeat (expand)
end P
variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : Fintype Bool := Bool.fintype

def Canonical (f : Signature K 2) : Prop :=
  f ![false,false]≠0 ∧ f ![false,true]≠0 ∧ f ![true,false]≠0 ∧ f ![true,true]=0

def factor (f : Signature K 2) (r : R.Raw) (x : Fin r.variables→Bool) (i : Fin r.edges.length) : K :=
  f ![R.extend x (r.edges.get i).1,R.extend x (r.edges.get i).2]

def value (f : Signature K 2) (r : R.Raw) : K :=
  ∑x : Fin r.variables→Bool,(r.edges.map (fun e=>f ![R.extend x e.1,R.extend x e.2])).prod

theorem factors_product (f : Signature K 2) (r : R.Raw) (x : Fin r.variables→Bool) :
    (∏i,factor f r x i)=(r.edges.map (fun e=>f ![R.extend x e.1,R.extend x e.2])).prod := by
  rw [←List.prod_ofFn]
  change (List.ofFn ((fun e : ℕ×ℕ=>f ![R.extend x e.1,R.extend x e.2]) ∘ r.edges.get)).prod=_
  rw [←List.map_ofFn,List.ofFn_get]

theorem value_factors (f : Signature K 2) (r : R.Raw) : value f r=∑x,∏i,factor f r x i := by
  simp_rw [factors_product]
  rfl

theorem program_assignment (r : R.Raw) (x : Fin r.variables→Bool) (i : ℕ) :
    BinaryCSPProgrammeValue.assignment r x i=R.extend x i := by
  by_cases hi : i<r.variables
  · rw [BinaryCSPProgrammeValue.assignment,List.getD_eq_getElem _ _ (by simpa using hi),
      R.extend,dite_eq_left hi]
    simp
  · rw [BinaryCSPProgrammeValue.assignment,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
      R.extend,dite_eq_right hi]

/-- The arithmetic programme and the finite proof use identical field values. -/
theorem program_value (f : Signature K 2) (r : R.Raw) :
    BinaryCSPProgrammeValue.value (fun x y=>f ![x,y]) r=value f r := by
  unfold BinaryCSPProgrammeValue.value BinaryCSPProgrammeValue.weight value
  simp only [program_assignment]

theorem support_product {I : Type*} [Fintype I] (u : I→K) :
    (if (∏i,u i)=0 then (0 : K) else 1)=∏i,if u i=0 then (0 : K) else 1 := by
  classical
  by_cases h : (∏i,u i)=0
  · rw [ite_eq_left h]
    symm
    obtain ⟨i,hi,hz⟩ := Finset.prod_eq_zero_iff.mp h
    exact Finset.prod_eq_zero hi (by simp [hz])
  · rw [ite_eq_right h]
    symm
    apply Finset.prod_eq_one
    intro i hi
    rw [ite_eq_right ((Finset.prod_ne_zero_iff.mp h) i hi)]

theorem support_entry (f : Signature K 2) (hf : Canonical f) (x y : Bool) :
    (if f ![x,y]=0 then (0 : K) else 1)=G.nand x y := by
  rcases hf with ⟨h0,h1,h2,h3⟩
  cases x <;> cases y <;> simp [h0,h1,h2,h3,G.nand]

theorem unsigned_support (f : Signature K 2) (hf : Canonical f) (r : R.Raw) (hs : r.signs=[]) :
    R.value (K:=K) r=∑x,if (∏i,factor f r x i)=0 then (0 : K) else 1 := by
  unfold R.value
  apply Finset.sum_congr rfl
  intro x _
  rw [support_product]
  simp_rw [factor,support_entry f hf]
  simp only [R.rowsWeight,hs,List.map_nil,List.prod_nil,mul_one]
  have h := factors_product (fun z=>G.nand (K:=K) (z 0) (z 1)) r x
  simpa only [factor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] using h.symm

theorem repeat_value (f : Signature K 2) (r : R.Raw) (k : ℕ) :
    value f (P.expand r k)=value (fun z=>f z^(k+1)) r := by
  unfold value
  apply Finset.sum_congr rfl
  intro x _
  change ((r.edges.flatMap (List.replicate (k+1))).map
    (fun e=>f ![R.extend x e.1,R.extend x e.2])).prod=_
  induction r.edges with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_replicate,
      List.prod_replicate,List.map_cons,List.prod_cons]
    rw [ih]

/-- Arbitrary nonzero original complex weights are removed by the actual
positive-repetition samples. Neither positivity nor nonresonance is assumed. -/
theorem unsigned_filter (f : Signature K 2) (hf : Canonical f) (r : R.Raw) (hs : r.signs=[]) :
    R.value (K:=K) r=(2 : K)^r.variables-
      D.differenceFilter (F.cubeRoots r.edges.length
        (f ![false,false]) (f ![false,true]) (f ![true,false]))
        (fun j=>value (fun z=>f z^j) r) 0 /
      F.denominator (F.cubeRoots r.edges.length
        (f ![false,false]) (f ![false,true]) (f ![true,false])) := by
  rw [unsigned_support f hf r hs]
  have hchoices (x : Fin r.variables→Bool) (i : Fin r.edges.length) :
      factor f r x i=0 ∨ factor f r x i=f ![false,false] ∨
      factor f r x i=f ![false,true] ∨ factor f r x i=f ![true,false] := by
    unfold factor
    cases R.extend x (r.edges.get i).1 <;> cases R.extend x (r.edges.get i).2 <;>
      simp [hf.2.2.2]
  have h := F.count_constraints (factor f r) hf.1 hf.2.1 hf.2.2.1 hchoices
  have hp (j : ℕ) : (∑x,∏i,factor f r x i^j)=value (fun z=>f z^j) r := by
    rw [value_factors]
    rfl
  simpa only [hp,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

theorem unsigned_filter_program (f : Signature K 2) (hf : Canonical f) (r : R.Raw) (hs : r.signs=[]) :
    R.value (K:=K) r=(2 : K)^r.variables-
      D.differenceFilter (F.cubeRoots r.edges.length
        (f ![false,false]) (f ![false,true]) (f ![true,false]))
        (fun j=>BinaryCSPProgrammeValue.value (fun x y=>f ![x,y]^j) r) 0 /
      F.denominator (F.cubeRoots r.edges.length
        (f ![false,false]) (f ![false,true]) (f ![true,false])) := by
  have hp (j : ℕ) : BinaryCSPProgrammeValue.value (fun x y=>f ![x,y]^j) r=
      value (fun z=>f z^j) r := program_value (fun z=>f z^j) r
  simpa only [hp] using unsigned_filter f hf r hs

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportWeights
