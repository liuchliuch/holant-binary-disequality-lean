import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedSignedPorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalSignedMultiplicityPhase

/-! At every even character multiplicity, the exact opposite-fourth anti
weight differs from every supported local twist by a full Affine coordinate
product. This statement is independent of the support rank. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalEvenCharacterPhase
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXLocalSignedMultiplicityPhase (unitPhase original grouped count unitPhase_nonzero)
end P
namespace W
export NoXWeightedSignedPorts (portWeight weight portWeight_ne_zero weight_ne_zero)
end W
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
export NoXSeparateSignedProjection (signedCount)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m : ℕ}
variable (v w : AlgebraicComplex)

def phaseAt (q : Port m) (a z : Fin m→Bool) : AlgebraicComplex :=
  match q with
  | .inl bit=>P.unitPhase bit
  | .inr (j,sgn)=>P.unitPhase ((sgn ^^ a j)&&(sgn ^^ z j))

def ratio (q : Port m) (a z : Fin m→Bool) : AlgebraicComplex := W.portWeight v w q z/phaseAt q a z

def gauge (ps : Fin n→Port m) (a z : Fin m→Bool) : AlgebraicComplex := ∏i,ratio v w (ps i) a z

def axisValue (a : Fin m→Bool) (j : Fin m) (bit sgn : Bool) : AlgebraicComplex :=
  (if sgn then (if bit then v else w) else 1)/P.unitPhase ((sgn ^^ a j)&&(sgn ^^ bit))

def axisGauge (ps : Fin n→Port m) (a : Fin m→Bool) (j : Fin m) (bit : Bool) : AlgebraicComplex :=
  ∏sgn : Bool,axisValue v w a j bit sgn^I.signedCount ps j sgn

def scalar (ps : Fin n→Port m) : AlgebraicComplex :=
  ∏bit : Bool,(P.unitPhase bit)⁻¹^P.count ps (.inl bit)

theorem grouped (ps : Fin n→Port m) (a z : Fin m→Bool) :
    gauge v w ps a z=scalar ps*∏j,axisGauge v w ps a j (z j) := by
  rw [gauge,P.grouped ps (fun q=>ratio v w q a z)]
  simp only [Fintype.prod_sum_type,Fintype.prod_prod_type,ratio,phaseAt,W.portWeight,
    one_div,scalar,axisGauge,axisValue,P.count,I.signedCount]
  congr 1

theorem phaseAt_nonzero (q : Port m) (a z : Fin m→Bool) : phaseAt q a z≠0 := by
  cases q with
  | inl bit=>exact P.unitPhase_nonzero bit
  | inr pair=>exact P.unitPhase_nonzero _

theorem split (ps : Fin n→Port m) (a z : Fin m→Bool) :
    W.weight v w ps z=gauge v w ps a z*P.original ps a z := by
  have he : P.original ps a z=∏i,phaseAt (ps i) a z := by
    apply Finset.prod_congr rfl
    intro i _
    cases h : ps i with
    | inl bit=>cases bit <;> simp [phaseAt,word,h,P.unitPhase]
    | inr pair=>rcases pair with ⟨j,sgn⟩;simp [word,h,phaseAt]
  rw [he,gauge,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (div_mul_cancel₀ _ (phaseAt_nonzero (ps i) a z)).symm

theorem totalCount (ps : Fin n→Port m) (j : Fin m) :
    (∑sgn : Bool,I.signedCount ps j sgn)=I.bundleSize ps j := by
  unfold I.signedCount I.bundleSize
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases h : ps i with
  | inl bit=>simp
  | inr pair=>
      rcases pair with ⟨k,sgn⟩
      by_cases hk : k=j <;> cases sgn <;> simp [hk]

variable (fourth : v^4= -(w^4))
include fourth in
theorem axisValue_fourth (a : Fin m→Bool) (j : Fin m) (sgn : Bool) :
    axisValue v w a j false sgn^4=(if a j then -1 else 1)*axisValue v w a j true sgn^4 := by
  cases sgn <;> cases ha : a j <;>
    simp [axisValue,ha,P.unitPhase,div_pow,zetaEight_pow_four,fourth,div_neg,div_one]

include fourth in
theorem axisPower_fourth (ps : Fin n→Port m) (a : Fin m→Bool) (j : Fin m) (sgn : Bool) :
    (axisValue v w a j false sgn^I.signedCount ps j sgn)^4=
      (if a j then -1 else 1)^I.signedCount ps j sgn*
      (axisValue v w a j true sgn^I.signedCount ps j sgn)^4 := by
  rw [pow_right_comm,axisValue_fourth v w fourth,mul_pow,pow_right_comm (axisValue v w a j true sgn)]

include fourth in
theorem axisGauge_fourth (ps : Fin n→Port m) (a : Fin m→Bool) (j : Fin m)
    (even : Even (I.bundleSize ps j)) : axisGauge v w ps a j false^4=axisGauge v w ps a j true^4 := by
  rw [axisGauge,←Finset.prod_pow]
  simp_rw [axisPower_fourth v w fourth]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,totalCount]
  cases a j <;> simp [even.neg_one_pow,axisGauge,mul_pow]

variable (hv : v≠0) (hw : w≠0)
include hv hw in
theorem axisValue_nonzero (a : Fin m→Bool) (j : Fin m) (bit sgn : Bool) : axisValue v w a j bit sgn≠0 := by
  apply div_ne_zero
  · cases sgn <;> cases bit <;> simp [hv,hw]
  · exact P.unitPhase_nonzero _

include hv hw in
theorem axisGauge_nonzero (ps : Fin n→Port m) (a : Fin m→Bool) (j : Fin m) (bit : Bool) :
    axisGauge v w ps a j bit≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun sgn _=>pow_ne_zero _ (axisValue_nonzero v w hv hw a j bit sgn))

include hv hw in
theorem gauge_nonzero (ps : Fin n→Port m) (a z : Fin m→Bool) : gauge v w ps a z≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact div_ne_zero (W.portWeight_ne_zero v w hv hw (ps i) z) (phaseAt_nonzero (ps i) a z)

include fourth hv hw in
theorem gauge_affine (ps : Fin n→Port m) (even : ∀j,Even (I.bundleSize ps j)) (a : Fin m→Bool) :
    Affine (gauge v w ps a) := by
  have ha (j : Fin m) : Affine (fun z : Fin m→Bool=>axisGauge v w ps a j (z j)) := by
    convert GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers j
      (axisGauge v w ps a j false) (axisGauge v w ps a j true)
      (axisGauge_nonzero v w hv hw ps a j false) (axisGauge_fourth v w fourth ps a j (even j)) using 1
    funext z
    cases z j <;> rfl
  have hh := (OrdinaryNegativeSignedRowsUniform.affine_prod Finset.univ
    (fun j z=>axisGauge v w ps a j (z j)) (fun j _=>ha j)).scale (scalar ps)
  convert hh using 1
  funext z
  exact grouped v w ps a z


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalEvenCharacterPhase
end
