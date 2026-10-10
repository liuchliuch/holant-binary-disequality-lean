import Holant.Proofs.Hardness.SparseUnitLocal

/-!
# Same-q unit macros for a dense EO six-vertex signature

The original q vanishes off weight two, and all six actual middle coefficients
are nonzero. Fixing original port3 gives weighted ONE(w,c,b) and TWO(d,z,y).
Both normalizing binaries are obtained by pinning that same cubic once more;
there are no algebraic inverse vertices or supplied normalization certificates.
The result has3 original q vertices,5 unary pins and7 native-X edges. Its exact
scales are w*c*b and d*z*y. This file grants no free or original-q unary access.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOUnitLocal
open Holant Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
namespace U
export SparseUnitLocal
  (pin pinned pinned_value pinNetwork pinNetwork_value weighted attach attach_anti unit ONE TWO)
end U
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains
  (reindex reindex_denote binarySignature)
end Chain
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

def EOSupport (q : Signature K 4) : Prop := ∀x,weight x≠2 → q x=0

def NonzeroMiddle (q : Signature K 4) : Prop :=
  (entries q).b≠0 ∧ (entries q).c≠0 ∧ (entries q).d≠0 ∧
  (entries q).w≠0 ∧ (entries q).z≠0 ∧ (entries q).y≠0

theorem even (q : Signature K 4) (hq : EOSupport q) : EvenSupport q := by
  intro x hx
  apply hq x
  omega

theorem corners_zero (q : Signature K 4) (hq : EOSupport q) :
    (entries q).a=0 ∧ (entries q).x=0 :=
  ⟨hq _ (by decide),hq _ (by decide)⟩

def cubeOrder (one : Bool) : Equiv.Perm (Fin 4) where
  toFun := if one then ![1,2,3,0] else ![0,1,3,2]
  invFun := if one then ![3,0,1,2] else ![0,1,3,2]
  left_inv := by intro i; cases one <;> fin_cases i <;> rfl
  right_inv := by intro i; cases one <;> fin_cases i <;> rfl

def cube (q : Signature K 4) (one : Bool) : Network K 3 :=
  U.pinned one (Chain.reindex (Network.corolla q) (cubeOrder one))

theorem cube_literal (q : Signature K 4) (one : Bool) (x : Fin 3 → Bool) :
    (cube q one).denote x=q ![x 0,x 1,x 2,one] := by
  rw [cube,U.pinned_value]
  cases one <;> simp only [Bool.false_eq_true,if_false,if_true,Chain.reindex_denote,
    Network.denote_corolla,Tensor.reindex_apply]
  all_goals apply congrArg q; funext i; fin_cases i <;> rfl

def weights (q : Signature K 4) (one : Bool) : Fin 3 → K :=
  if one then ![(entries q).w,(entries q).c,(entries q).b]
  else ![(entries q).d,(entries q).z,(entries q).y]

theorem cube_value (q : Signature K 4) (hq : EOSupport q) (one : Bool) :
    (cube q one).denote=U.weighted one (weights q one) := by
  have ht := table_entries q (even q hq)
  have hz := corners_zero q hq
  funext x
  rw [cube_literal,←ht]
  cases one <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [table,U.weighted,weights,entries,h0,h1,h2] at *
  all_goals first | exact hz.1 | exact hz.2

theorem weights_nonzero (q : Signature K 4) (hn : NonzeroMiddle q) (one : Bool) (i : Fin 3) :
    weights q one i≠0 := by
  rcases hn with ⟨hb,hc,hd,hw,hz,hy⟩
  cases one <;> fin_cases i
  all_goals simp only [weights,if_true,if_false,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals assumption

def swap01 : Equiv.Perm (Fin 3) where
  toFun := ![1,0,2]
  invFun := ![1,0,2]
  left_inv := by decide
  right_inv := by decide

def binary0 (q : Signature K 4) (one : Bool) : Network K 2 :=
  U.pinNetwork one (Chain.reindex (cube q one) swap01)
def binary1 (q : Signature K 4) (one : Bool) : Network K 2 := U.pinNetwork one (cube q one)

theorem binary0_value (q : Signature K 4) (hq : EOSupport q) (one : Bool) :
    (binary0 q one).denote=Chain.binarySignature (weightedX
      (if one then weights q one 2 else weights q one 0)
      (if one then weights q one 0 else weights q one 2)) := by
  funext x
  rw [binary0,U.pinNetwork_value]
  cases one <;> simp only [Bool.false_eq_true,if_false,if_true,Chain.reindex_denote,cube_value q hq]
  all_goals cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [U.weighted,Chain.binarySignature,weightedX,Tensor.reindex_apply,swap01,h0,h1]

theorem binary1_value (q : Signature K 4) (hq : EOSupport q) (one : Bool) :
    (binary1 q one).denote=Chain.binarySignature (weightedX
      (if one then weights q one 2 else weights q one 1)
      (if one then weights q one 1 else weights q one 2)) := by
  funext x
  rw [binary1,U.pinNetwork_value]
  cases one <;> simp only [Bool.false_eq_true,if_false,if_true,cube_value q hq]
  all_goals cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [U.weighted,Chain.binarySignature,weightedX,h0,h1]

def unitNetwork (q : Signature K 4) (one : Bool) : Network K 3 :=
  U.attach (U.attach (cube q one) (binary0 q one) 0) (binary1 q one) 1

abbrev unit (one : Bool) : Signature K 3 := U.unit one

def scale (q : Signature K 4) (one : Bool) : K :=
  (weights q one 0*weights q one 1)*weights q one 2

theorem unit_value (q : Signature K 4) (hq : EOSupport q) (one : Bool) :
    (unitNetwork q one).denote=scale q one • U.unit one := by
  funext x
  rw [unitNetwork,U.attach_anti _ _ 1 _ _ (binary1_value q hq one),
    U.attach_anti _ _ 0 _ _ (binary0_value q hq one),cube_value q hq one]
  cases one <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [U.unit,scale,U.weighted,U.ONE,U.TWO,Pi.smul_apply,smul_eq_mul,h0,h1,h2] <;>
      first | trivial | ring
  all_goals simp

theorem scale_nonzero (q : Signature K 4) (hn : NonzeroMiddle q) (one : Bool) : scale q one≠0 :=
  mul_ne_zero (mul_ne_zero (weights_nonzero q hn one 0) (weights_nonzero q hn one 1))
    (weights_nonzero q hn one 2)

theorem scales_exact (q : Signature K 4) :
    scale q true=(entries q).w*(entries q).c*(entries q).b ∧
    scale q false=(entries q).d*(entries q).z*(entries q).y := ⟨rfl,rfl⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOUnitLocal
