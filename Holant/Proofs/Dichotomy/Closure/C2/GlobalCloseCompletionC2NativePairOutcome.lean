import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairOutcome
import Holant.Proofs.Hardness.GeneralEOAffineNetworkChain
import Holant.Proofs.Hardness.GeneralEOPinnedDescentAccess

/-! The complementary native EO pair has an actual finite DEQ graph or a
counted Ising reduction. All chain labels and edge subdivisions are compiled
from the given graph in the unchanged coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2NativePairOutcome
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace P
export GlobalCloseCompletionC2OrdinaryPairPowers (equal_eigenpowers fourth_residual_period plus_nonzero)
end P
namespace M
export GeneralEOAffinePlaneChain (binary table bitIndex copies copies_denote)
end M
namespace L
export GeneralEOAffinePlaneChainLabels (copies copies_exact)
end L
namespace S
export GlobalCloseCompletionKleinOrdinaryPair (symmetric)
end S
namespace E
export OrdinarySymmetricPairEscape (step escape)
end E
namespace A
export GeneralEOPinnedDescentAccess (source targetValue)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K]
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable {degree s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (arity i.val))

structure Macro where
  network : Network K 4
  labels : Labelling network.shape s 1 arity
  exact : LabelledNetwork.Exact H network labels
  native : ∀e,network.edge e=Signature.disequality

def powerMacro (N : Macro H) (k : ℕ) : Macro H where
  network := M.copies N.network k
  labels := L.copies N.network N.labels k
  exact := L.copies_exact H N.network N.labels N.exact k
  native := GeneralEOAffinePlaneChain.copies_native N.network N.native k

def HasDEQ : Prop := Nonempty (GeneralEODEQProducerNormalize.Produced H)

theorem deq_of_period (N : Macro H) (a d : K)
    (form : N.network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric a d)))
    (mu : a+d≠0) (t : ℕ) (positive : 0<t) (period : ((a-d)/(a+d))^t=1) : HasDEQ H := by
  have ht : t-1+1=t := by omega
  have powers : (a-d)^t=(a+d)^t := by
    rw [div_pow] at period
    exact (div_eq_one_iff_eq (pow_ne_zero _ mu)).mp period
  refine ⟨⟨(powerMacro H N (t-1)).network,(powerMacro H N (t-1)).labels,
    (powerMacro H N (t-1)).exact,(powerMacro H N (t-1)).native,(a+d)^t,
    pow_ne_zero _ mu,?_⟩⟩
  change (M.copies N.network (t-1)).denote=_
  rw [M.copies_denote _ _ form,ht,P.equal_eigenpowers a d t powers,
    GeneralEOAffinePlaneDEQ.lifted_scalar]

theorem double_form (N : Macro H) (a d : K)
    (form : N.network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric a d))) :
    (powerMacro H N 1).network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric (a^2+d^2) (2*a*d))) := by
  rw [powerMacro,M.copies_denote _ _ form]
  have matrix : S.symmetric a d ^ 2=S.symmetric (a^2+d^2) (2*a*d) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two,S.symmetric,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  rw [matrix]

theorem binary_ising (a d : K) : M.binary (S.symmetric a d)=BinaryIsingWeights.table a d := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [M.binary,M.bitIndex,S.symmetric,BinaryIsingWeights.table,BinaryIsingWeights.interaction,h0,h1]

def source (N : Macro H) (a d : K)
    (form : N.network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric a d)))
    (ha : a≠0) (hd : d≠0) (infinite : ∀n : ℕ,0<n→(d/a)^n≠1)
    {α : Type} {ea : Encoding α Bool} {count : α→ℕ} (w : SharpPWitness ea count) :
    LengthControlledOracleReduction ea encodingNatBool
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding count (A.targetValue F H) :=
  Programme.compose
    (BinaryIsingCountingSource.source F N.network.denote a d
      (form.trans (congrArg EOBinaryPlaneCore.lift (binary_ising a d))) ha hd
      (fun n hn=>infinite (2*n) (by omega)) w)
    (A.source F H N.network N.labels N.exact N.native)

theorem countingHard (N : Macro H) (a d : K)
    (form : N.network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric a d)))
    (ha : a≠0) (hd : d≠0) (infinite : ∀n : ℕ,0<n→(d/a)^n≠1) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding (A.targetValue F H) := by
  intro α ea count w
  exact ⟨(source F H N a d form ha hd infinite w).reduction⟩

variable (phi : K→+*ℂ) (N : Macro H)
variable (a d : K) (form : N.network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric a d)))
variable (determinant : a^2≠d^2)

include phi form determinant in
theorem deq_or_hard : HasDEQ H ∨ Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (A.targetValue F H) := by
  classical
  have mu := P.plus_nonzero a d determinant
  by_cases ha : a=0
  · left
    have hd : d≠0 := by simpa [ha] using mu
    apply deq_of_period H N a d form mu 2 (by omega)
    simp [ha,hd]
  by_cases hd : d=0
  · left
    apply deq_of_period H N a d form mu 1 (by omega)
    simp [hd,ha]
  by_cases negative : (d/a)^2= -1
  · left
    have square : d^2= -a^2 := by
      have h : d^2/a^2= -1 := by simpa only [div_pow] using negative
      simpa only [neg_one_mul] using (div_eq_iff (pow_ne_zero _ ha)).mp h
    have fourth : d^4=a^4 := by
      calc
        d^4=(d^2)^2 := by ring
        _=(-a^2)^2 := by rw [square]
        _=a^4 := by ring
    exact deq_of_period H N a d form mu 4 (by omega) (P.fourth_residual_period a d determinant fourth)
  have notOne : (phi (d/a))^2≠1 := by
    intro h
    have eqn : (d/a)^2=1 := phi.injective (by simpa only [map_pow,map_one] using h)
    have square : d^2=a^2 := (div_eq_one_iff_eq (pow_ne_zero _ ha)).mp (by simpa only [div_pow] using eqn)
    exact determinant square.symm
  have notNegative : (phi (d/a))^2≠ -1 := by
    intro h
    apply negative
    apply phi.injective
    simpa only [map_pow,map_neg,map_one] using h
  rcases E.escape (phi (d/a)) notOne notNegative with first | ⟨_denom,second⟩
  · right
    exact countingHard F H N a d form ha hd
      (GlobalCloseCompletionC2OrdinaryPairOutcome.infinite_of_image phi (d/a) first)
  · right
    have leftNonzero : a^2+d^2≠0 := by
      intro zero
      apply negative
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero _ ha)).mpr
      linear_combination zero
    have rightNonzero : 2*a*d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hd
    have ratio : phi ((2*a*d)/(a^2+d^2))=E.step (phi (d/a)) := by
      have nonzeroA : phi a≠0 := (map_ne_zero phi).mpr ha
      have nonzeroSum : phi a^2+phi d^2≠0 := by
        simpa only [map_add,map_pow] using (map_ne_zero phi).mpr leftNonzero
      calc
        phi ((2*a*d)/(a^2+d^2))=(2*phi a*phi d)/(phi a^2+phi d^2) := by
          rw [_root_.map_div₀,phi.map_mul,phi.map_mul,phi.map_add,_root_.map_pow,_root_.map_pow,_root_.map_ofNat]
        _=E.step (phi (d/a)) := by
          rw [E.step,_root_.map_div₀]
          field_simp [nonzeroA,nonzeroSum]
    apply countingHard F H (powerMacro H N 1)
      (a^2+d^2) (2*a*d) (double_form H N a d form) leftNonzero rightNonzero
    apply GlobalCloseCompletionC2OrdinaryPairOutcome.infinite_of_image phi
    rw [ratio]
    exact second

section Target
variable {β V : Type} (eb : Encoding β Bool) (ev : Encoding V Bool) (value : β→V)
variable (R : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
  eb ev (A.targetValue F H) value)

include R in
theorem countingHardTo (N : Macro H) (a d : K)
    (form : N.network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric a d)))
    (ha : a≠0) (hd : d≠0) (infinite : ∀n : ℕ,0<n→(d/a)^n≠1) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard eb ev value := by
  intro α ea count w
  exact ⟨(source F H N a d form ha hd infinite w).compose R.reduction⟩

include R phi form determinant in
theorem deq_or_hard_to : HasDEQ H ∨ Holant.LocalDrafts.CountingHardness.WitnessCountingHard eb ev value := by
  classical
  have mu := P.plus_nonzero a d determinant
  by_cases ha : a=0
  · left
    have hd : d≠0 := by simpa [ha] using mu
    apply deq_of_period H N a d form mu 2 (by omega)
    simp [ha,hd]
  by_cases hd : d=0
  · left
    apply deq_of_period H N a d form mu 1 (by omega)
    simp [hd,ha]
  by_cases negative : (d/a)^2= -1
  · left
    have square : d^2= -a^2 := by
      have h : d^2/a^2= -1 := by simpa only [div_pow] using negative
      simpa only [neg_one_mul] using (div_eq_iff (pow_ne_zero _ ha)).mp h
    have fourth : d^4=a^4 := by
      calc
        d^4=(d^2)^2 := by ring
        _=(-a^2)^2 := by rw [square]
        _=a^4 := by ring
    exact deq_of_period H N a d form mu 4 (by omega) (P.fourth_residual_period a d determinant fourth)
  have notOne : (phi (d/a))^2≠1 := by
    intro h
    have eqn : (d/a)^2=1 := phi.injective (by simpa only [map_pow,map_one] using h)
    have square : d^2=a^2 := (div_eq_one_iff_eq (pow_ne_zero _ ha)).mp (by simpa only [div_pow] using eqn)
    exact determinant square.symm
  have notNegative : (phi (d/a))^2≠ -1 := by
    intro h
    apply negative
    apply phi.injective
    simpa only [map_pow,map_neg,map_one] using h
  rcases E.escape (phi (d/a)) notOne notNegative with first | ⟨_denom,second⟩
  · right
    exact countingHardTo F H eb ev value R N a d form ha hd
      (GlobalCloseCompletionC2OrdinaryPairOutcome.infinite_of_image phi (d/a) first)
  · right
    have leftNonzero : a^2+d^2≠0 := by
      intro zero
      apply negative
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero _ ha)).mpr
      linear_combination zero
    have rightNonzero : 2*a*d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hd
    have ratio : phi ((2*a*d)/(a^2+d^2))=E.step (phi (d/a)) := by
      have nonzeroA : phi a≠0 := (map_ne_zero phi).mpr ha
      have nonzeroSum : phi a^2+phi d^2≠0 := by
        simpa only [map_add,map_pow] using (map_ne_zero phi).mpr leftNonzero
      calc
        phi ((2*a*d)/(a^2+d^2))=(2*phi a*phi d)/(phi a^2+phi d^2) := by
          rw [_root_.map_div₀,phi.map_mul,phi.map_mul,phi.map_add,_root_.map_pow,_root_.map_pow,_root_.map_ofNat]
        _=E.step (phi (d/a)) := by
          rw [E.step,_root_.map_div₀]
          field_simp [nonzeroA,nonzeroSum]
    apply countingHardTo F H eb ev value R (powerMacro H N 1)
      (a^2+d^2) (2*a*d) (double_form H N a d form) leftNonzero rightNonzero
    apply GlobalCloseCompletionC2OrdinaryPairOutcome.infinite_of_image phi
    rw [ratio]
    exact second

end Target


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2NativePairOutcome
end
