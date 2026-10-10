import Holant.Proofs.Hardness.DenseEOUnitLocal

/-! Three-original-q unit macros under only four nonzero middle entries.
The first cube pins original port0 to1; the second pins original port2 to0.
Their ordered weights are(y,z,w) and(c,w,y). Thus b and d may vanish.
Both normalizing binaries are actual further pinnings of that same original
cube. No original-q pin access or pin-free hardness is asserted here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PartialEOUnitLocal
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

abbrev EOSupport (q : Signature K 4) := DenseEOUnitLocal.EOSupport q

def RequiredEntries (q : Signature K 4) : Prop :=
  (entries q).c≠0 ∧ (entries q).w≠0 ∧ (entries q).z≠0 ∧ (entries q).y≠0

export DenseEOUnitLocal (even corners_zero)

def cube (q : Signature K 4) (one : Bool) : Network K 3 :=
  U.pinned one (Network.corolla q)

theorem cube_literal (q : Signature K 4) (one : Bool) (x : Fin 3 → Bool) :
    (cube q one).denote x=
      if one then q ![true,x 0,x 1,x 2] else q ![x 0,x 1,false,x 2] := by
  simpa only [cube,Network.denote_corolla] using U.pinned_value one (Network.corolla q) x

def weights (q : Signature K 4) (one : Bool) : Fin 3 → K :=
  if one then ![(entries q).y,(entries q).z,(entries q).w]
  else ![(entries q).c,(entries q).w,(entries q).y]

theorem cube_value (q : Signature K 4) (hq : EOSupport q) (one : Bool) :
    (cube q one).denote=U.weighted one (weights q one) := by
  have ht := table_entries q (even q hq)
  have hz := corners_zero q hq
  funext x
  rw [cube_literal,←ht]
  cases one <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [table,U.weighted,weights,entries,h0,h1,h2] at *
  all_goals first | exact hz.1 | exact hz.2

theorem weights_nonzero (q : Signature K 4) (hn : RequiredEntries q) (one : Bool) (i : Fin 3) :
    weights q one i≠0 := by
  rcases hn with ⟨hc,hw,hz,hy⟩
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

theorem scale_nonzero (q : Signature K 4) (hn : RequiredEntries q) (one : Bool) : scale q one≠0 :=
  mul_ne_zero (mul_ne_zero (weights_nonzero q hn one 0) (weights_nonzero q hn one 1))
    (weights_nonzero q hn one 2)

theorem scales_exact (q : Signature K 4) :
    scale q true=(entries q).y*(entries q).z*(entries q).w ∧
    scale q false=(entries q).c*(entries q).w*(entries q).y := ⟨rfl,rfl⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PartialEOUnitLocal
