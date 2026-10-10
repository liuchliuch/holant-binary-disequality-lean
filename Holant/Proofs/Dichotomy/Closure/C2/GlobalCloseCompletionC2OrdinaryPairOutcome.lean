import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairIsing
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairPowers
import Holant.Proofs.Dichotomy.Ordinary.OrdinarySymmetricPairEscape

/-! A nonsingular ordinary symmetric pair with actual X has a finite exact
Eq4 graph or genuine Ising counting hardness. The one/two-copy choice and
all root-of-unity residuals are discharged internally from the actual entries. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairOutcome
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open OrdinaryNegativeCubicGadgets
namespace P
export GlobalCloseCompletionC2OrdinaryPairPowers
  (power labels exact ordinary power_denote period_denote fourth_residual_period plus_nonzero)
end P
namespace M
export GeneralEOAffinePlaneChain (binary)
end M
namespace S
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric)
end S
namespace E
export OrdinarySymmetricPairEscape (step escape)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K]
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable {degree s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (arity i.val))

def powerMacro (N : Macro H 4) (k : ℕ) : Macro H 4 where
  network := P.power N.network k
  labels := P.labels N.network N.labels k
  exact := P.exact H N.network N.labels N.exact k
  edges := P.ordinary N.network N.edges k

def HasEq4 : Prop := ∃N : Macro H 4,∃c : K,c≠0 ∧ N.network.denote=c • Holant.EightVertex.ProductAnchor.equalityFour

theorem eq4_of_period (N : Macro H 4) (a d : K)
    (form : N.network.denote=S.pair (M.binary (S.symmetric a d)))
    (mu : a+d≠0) (t : ℕ) (positive : 0<t) (period : ((a-d)/(a+d))^t=1) : HasEq4 H :=
  ⟨powerMacro H N (t-1),(a+d)^t,pow_ne_zero _ mu,P.period_denote N.network a d form mu t positive period⟩

theorem double_form (N : Macro H 4) (a d : K)
    (form : N.network.denote=S.pair (M.binary (S.symmetric a d))) :
    (powerMacro H N 1).network.denote=S.pair (M.binary (S.symmetric (a^2+d^2) (2*a*d))) := by
  rw [powerMacro,P.power_denote _ _ form]
  have matrix : S.symmetric a d ^ 2=S.symmetric (a^2+d^2) (2*a*d) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two,S.symmetric,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  rw [matrix]

theorem infinite_of_image (phi : K→+*ℂ) (r : K)
    (h : ∀ n : ℕ, 0 < n → (phi r) ^ n ≠ 1) : ∀ n : ℕ, 0 < n → (r ^ n) ≠ 1 := by
  intro n hn eqn
  apply h n hn
  rw [←map_pow,eqn,map_one]

variable (phi : K→+*ℂ) (N : Macro H 4) (j : Fin s)
variable (literal : (⟨arity j.val,H j⟩ : AnySignature K)=⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (a d : K) (form : N.network.denote=S.pair (M.binary (S.symmetric a d)))
variable (determinant : a^2≠d^2)

include phi literal form determinant in
theorem eq4_or_hard : HasEq4 H ∨ Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) := by
  classical
  have mu := P.plus_nonzero a d determinant
  by_cases ha : a=0
  · left
    have hd : d≠0 := by simpa [ha] using mu
    apply eq4_of_period H N a d form mu 2 (by omega)
    simp [ha,hd]
  by_cases hd : d=0
  · left
    apply eq4_of_period H N a d form mu 1 (by omega)
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
    exact eq4_of_period H N a d form mu 4 (by omega) (P.fourth_residual_period a d determinant fourth)
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
    exact GlobalCloseCompletionC2OrdinaryPairIsing.countingHard F H N j literal a d form ha hd
      (infinite_of_image phi (d/a) first)
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
    apply GlobalCloseCompletionC2OrdinaryPairIsing.countingHard F H (powerMacro H N 1) j literal
      (a^2+d^2) (2*a*d) (double_form H N a d form) leftNonzero rightNonzero
    apply infinite_of_image phi
    rw [ratio]
    exact second

section Target
variable {β V : Type} (eb : Encoding β Bool) (ev : Encoding V Bool) (value : β→V)
variable (R : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
  eb ev ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) value)

include R literal in
theorem countingHardTo (N : Macro H 4) (a d : K)
    (form : N.network.denote=S.pair (M.binary (S.symmetric a d)))
    (ha : a≠0) (hd : d≠0) (infinite : ∀n : ℕ,0<n→(d/a)^n≠1) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard eb ev value := by
  intro α ea count w
  exact ⟨(GlobalCloseCompletionC2OrdinaryPairIsing.source F H N j literal a d form ha hd infinite w).compose R.reduction⟩

include R phi literal form determinant in
theorem eq4_or_hard_to : HasEq4 H ∨ Holant.LocalDrafts.CountingHardness.WitnessCountingHard eb ev value := by
  classical
  have mu := P.plus_nonzero a d determinant
  by_cases ha : a=0
  · left
    have hd : d≠0 := by simpa [ha] using mu
    apply eq4_of_period H N a d form mu 2 (by omega)
    simp [ha,hd]
  by_cases hd : d=0
  · left
    apply eq4_of_period H N a d form mu 1 (by omega)
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
    exact eq4_of_period H N a d form mu 4 (by omega) (P.fourth_residual_period a d determinant fourth)
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
    exact countingHardTo F H j literal eb ev value R N a d form ha hd
      (infinite_of_image phi (d/a) first)
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
    apply countingHardTo F H j literal eb ev value R (powerMacro H N 1)
      (a^2+d^2) (2*a*d) (double_form H N a d form) leftNonzero rightNonzero
    apply infinite_of_image phi
    rw [ratio]
    exact second

end Target


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairOutcome
end
