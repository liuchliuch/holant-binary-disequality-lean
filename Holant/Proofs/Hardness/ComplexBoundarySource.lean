import Holant.Proofs.Hardness.ComplexBoundaryStageAccess
import Holant.Proofs.Hardness.PositiveBoundarySource

/-! Every nonzero complex selfdual boundary c=a+b has an original-oracle
hard source. Equal side coefficients use the accepted two-coefficient source.
Unequal spectral moduli give interpolation directly; equal moduli use a
literal two-original-vertex escape. No spectral or arithmetic promise is input.
The complex embedding is only used in the proof; every oracle answer uses F. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexBoundarySource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace E
export ComplexBoundaryEscape (first second third boundary)
end E
namespace I
export PositiveBoundaryInterpolation (targetValue)
end I
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (φ : K →+* ℂ) (a b : K)
local instance fieldCharZero : CharZero K := algebraRat.charZero K

omit [Algebra ℚ K] in
theorem mapped_nonzero (x : K) (hx : x≠0) : φ x≠0 := by
  intro hz
  exact hx (φ.injective (by simpa only [map_zero] using hz))

theorem infinite_of_unequal (c ν : K) (hν : ν≠0) (h : ‖φ c‖≠‖φ ν‖)
    (n : ℕ) (hn : 0<n) : (c/ν)^n≠1 := by
  intro he
  apply GeneralGeometricCapLocal.infinite_of_unequal_norms (φ c) (φ ν)
    (mapped_nonzero φ ν hν) h n hn
  simpa only [map_pow,map_div₀,map_one] using congrArg φ he

@[simp] theorem map_first : φ (E.first a b)=E.first (φ a) (φ b) := by
  simp only [E.first,map_mul,map_add,map_ofNat]
omit [Algebra ℚ K] in
@[simp] theorem map_second : φ (E.second a b)=E.second (φ a) (φ b) := by
  simp only [E.second,map_pow]
@[simp] theorem map_third : φ (E.third a b)=E.third (φ a) (φ b) := by
  simp only [E.third,map_pow,map_add]

theorem escape_nonzero (ha : a≠0) (hb : b≠0)
    (h : ‖φ (a+b)‖=‖φ (b-a)‖) : E.third a b≠0 ∧ E.second a b-E.first a b≠0 := by
  have hc : ‖φ a+φ b‖=‖φ b-φ a‖ := by simpa only [map_add,map_sub] using h
  constructor
  · intro hz
    apply ComplexBoundaryEscape.third_nonzero (φ a) (φ b) (mapped_nonzero φ a ha) hc
    simpa only [map_third,map_zero] using congrArg φ hz
  · intro hz
    apply ComplexBoundaryEscape.difference_nonzero (φ a) (φ b)
      (mapped_nonzero φ a ha) (mapped_nonzero φ b hb) hc
    simpa only [map_sub,map_second,map_first,map_zero] using congrArg φ hz

theorem escape_infinite (ha : a≠0) (hb : b≠0)
    (h : ‖φ (a+b)‖=‖φ (b-a)‖) (n : ℕ) (hn : 0<n) :
    (E.third a b/(E.second a b-E.first a b))^n≠1 := by
  intro hz
  apply ComplexBoundaryEscape.ratio_infinite (φ a) (φ b)
    (mapped_nonzero φ a ha) (mapped_nonzero φ b hb)
    (by simpa only [map_add,map_sub] using h) n hn
  simpa only [map_pow,map_div₀,map_sub,map_third,map_second,map_first,map_one] using congrArg φ hz

/-- The accepted hard H is physically included and then eliminated by actual chains. -/
def interpolation (c : K) (hc : c=a+b) (hc0 : c≠0) (hν : b-a≠0)
    (hinf : ∀n : ℕ,0<n → (c/(b-a))^n≠1) :
    LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
      ExactTwoChainQueries.targetEncoding F.encoding
      (SparseUnitValue.value (K:=K)) (I.targetValue a b c) :=
  Compose.composeControlled
    (Compose.composeControlled
      (TwoCoefficientSource.source F (1 : K) (1/2) (by norm_num) (by norm_num))
      (PositiveBoundarySource.inclusion F a b c))
    (PositiveBoundaryInterpolation.source a b c hc hc0 hν hinf F)

/-- A genuine embedding into complex numbers suffices; no norm or spectral datum
is assumed on K, and both sides keep the exact same coefficient presentation. -/
def sourceWithEmbedding (ha : a≠0) (hb : b≠0) (hc : a+b≠0) :
    LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
      ExactTwoChainQueries.targetEncoding F.encoding
      (SparseUnitValue.value (K:=K)) (I.targetValue a b (a+b)) := by
  classical
  by_cases hν : b-a=0
  · have hba : b=a := sub_eq_zero.mp hν
    subst b
    exact TwoCoefficientSource.source F (a+a) a hc ha
  · by_cases hmod : ‖φ (a+b)‖=‖φ (b-a)‖
    · have hn := escape_nonzero φ a b ha hb hmod
      let r := interpolation F (E.first a b) (E.second a b) (E.third a b)
        (E.boundary a b) hn.1 hn.2 (escape_infinite φ a b ha hb hmod)
      exact Compose.composeControlled r (ComplexBoundaryStageAccess.source F a b)
    · exact interpolation F a b (a+b) rfl hc hν (infinite_of_unequal φ (a+b) (b-a) hν hmod)

/-- For an arbitrary fixed finite rational presentation, the embedding is
constructed internally. The only scalar assumptions are a,b,a+b nonzero. -/
def source (ha : a≠0) (hb : b≠0) (hc : a+b≠0) :
    LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
      ExactTwoChainQueries.targetEncoding F.encoding
      (SparseUnitValue.value (K:=K)) (I.targetValue a b (a+b)) :=
  sourceWithEmbedding F (TwoCoefficientRatioEscape.embedding F).toRingHom a b ha hb hc

attribute [local irreducible] source sourceWithEmbedding

def outputs (ha : a≠0) (hb : b≠0) (hc : a+b≠0) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle ExactTwoChainQueries.targetEncoding F.encoding (I.targetValue a b (a+b)) oracle)
    (r : SparseUnitValue.Input) :=
  (source F a b ha hb hc).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexBoundarySource
