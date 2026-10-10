import Holant.Proofs.Hardness.EqualModulusThreeModeInfiniteSource
import Holant.Proofs.Hardness.EqualModulusThreeModeStageAccess
import Holant.Proofs.Hardness.EqualModulusThreeModePortAccess
import Holant.Proofs.Hardness.ComplexBoundarySource

/-! Closed equal-modulus source. One original-field torsion test selects either
the actual full three-mode annihilator or an actual T-copy q chain followed by
the full complex boundary source. Every stage retains one fixed presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace A
export EqualModulusThreeModeLocal (exponent exponent_pos denominator_plus denominator_minus powered_sides_nonzero)
end A
namespace C
export EqualModulusThreeModeChain (first second third sum difference)
end C
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
namespace G
export ThreeModeGraphEvaluation (targetValue)
end G
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [NormedField K] [Algebra ℚ K] [FiniteDimensional ℚ K] {d : ℕ}
variable (F : FixedField K d) (φ : K →+* ℂ) (a b c : K)
local instance : CharZero K := algebraRat.charZero K

def Applicable : Prop :=
  (‖a+b‖=‖c‖ ∧ ‖b-a‖<‖c‖) ∨ (‖b-a‖=‖c‖ ∧ ‖a+b‖<‖c‖)

/-- The finite-test equality is an exact equality in the original field. -/
theorem test_power (p : K) (hc : c≠0) (h : (p/c)^A.exponent (K:=K)=1) :
    p^A.exponent (K:=K)=c^A.exponent (K:=K) := by
  rwa [div_pow,div_eq_one_iff_eq (pow_ne_zero _ hc)] at h

variable (ha : a≠0) (hb : b≠0) (hc : c≠0)

def finitePlus (he : ‖a+b‖=‖c‖) (hlt : ‖b-a‖<‖c‖)
    (htest : ((a+b)/c)^A.exponent (K:=K)=1) :
    LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
      ExactTwoChainQueries.targetEncoding F.encoding
      (SparseUnitValue.value (K:=K)) (G.targetValue a b c) := by
  let n := A.exponent (K:=K)
  have hn : 0<n := A.exponent_pos
  have hp := test_power c (a+b) hc htest
  have hgap : ‖b-a‖<‖a+b‖ := by rwa [he]
  have hab := A.powered_sides_nonzero (a+b) (b-a) n hn (Or.inl hgap)
  have hcT : C.third c n≠0 := pow_ne_zero _ hc
  have hs : C.first a b n+C.second a b n=C.third c n := (C.sum a b n).trans hp
  have r := ComplexBoundarySource.sourceWithEmbedding F φ (C.first a b n) (C.second a b n)
    hab.1 hab.2 (by rw [hs]; exact hcT)
  rw [hs] at r
  exact Compose.composeControlled r (EqualModulusThreeModeStageAccess.source F a b c n hn)

def finiteMinus (he : ‖b-a‖=‖c‖) (hlt : ‖a+b‖<‖c‖)
    (htest : ((b-a)/c)^A.exponent (K:=K)=1) :
    LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
      ExactTwoChainQueries.targetEncoding F.encoding
      (SparseUnitValue.value (K:=K)) (G.targetValue a b c) := by
  let n := A.exponent (K:=K)
  have hn : 0<n := A.exponent_pos
  have hp := test_power c (b-a) hc htest
  have hgap : ‖a+b‖<‖b-a‖ := by rwa [he]
  have hab := A.powered_sides_nonzero (a+b) (b-a) n hn (Or.inr hgap)
  have hcT : C.third c n≠0 := pow_ne_zero _ hc
  have hd : C.second a b n-C.first a b n=C.third c n := (C.difference a b n).trans hp
  have hs : C.first a b n+C.third c n=C.second a b n := by rw [←hd]; ring
  have r := ComplexBoundarySource.sourceWithEmbedding F φ (C.first a b n) (C.third c n)
    hab.1 hcT (by rw [hs]; exact hab.2)
  rw [hs] at r
  have port := EqualModulusThreeModePortAccess.source F
    (ThreeModeSignatures.original (C.first a b n) (C.second a b n) (C.third c n))
    SignedTwoCoefficientSignatures.middleSwap
  have hport : OriginalPortAccess.normalized
      (ThreeModeSignatures.original (C.first a b n) (C.second a b n) (C.third c n))
      SignedTwoCoefficientSignatures.middleSwap=
      ThreeModeSignatures.original (C.first a b n) (C.third c n) (C.second a b n) :=
    ThreeModeTriangleObstruction.swap_bc _ _ _
  rw [hport] at port
  exact Compose.composeControlled (Compose.composeControlled r port)
    (EqualModulusThreeModeStageAccess.source F a b c n hn)

/-- Both branches are selected internally from a finite original-field equality. -/
def source (h : Applicable a b c) :
    LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
      ExactTwoChainQueries.targetEncoding F.encoding
      (SparseUnitValue.value (K:=K)) (G.targetValue a b c) := by
  classical
  by_cases hplus : ‖a+b‖=‖c‖ ∧ ‖b-a‖<‖c‖
  · obtain ⟨he,hlt⟩ := hplus
    by_cases ht : ((a+b)/c)^A.exponent (K:=K)=1
    · exact finitePlus F φ a b c hc he hlt ht
    · exact EqualModulusThreeModeInfiniteSource.source F a b c ha hb hc
        (A.denominator_plus a b c hc he hlt ht)
  · have hminus := h.resolve_left hplus
    obtain ⟨he,hlt⟩ := hminus
    by_cases ht : ((b-a)/c)^A.exponent (K:=K)=1
    · exact finiteMinus F φ a b c hc he hlt ht
    · exact EqualModulusThreeModeInfiniteSource.source F a b c ha hb hc
        (A.denominator_minus a b c hc he hlt ht)

attribute [local irreducible] source

def outputs (h : Applicable a b c) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle ExactTwoChainQueries.targetEncoding F.encoding (G.targetValue a b c) oracle)
    (r : SparseUnitValue.Input) :=
  (source F φ a b c ha hb hc h).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeSource
