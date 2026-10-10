import Holant.Proofs.Hardness.EOBinaryPlaneIsingAccess
import Holant.Proofs.Hardness.EOBinaryPlanePositive
import Holant.Proofs.Hardness.BinaryIsingSource

/-! A genuinely positive nonsingular binary table supplies an actual unsigned
NAND-count reduction to its original quaternary lift. The complement-product
Ising gadget, unused-variable correction, one global apex factor, and machine
composition are internal. A complex embedding proves positivity only; every
oracle answer and arithmetic operation uses the supplied fixed field K. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositiveSource
open Holant Holant.Algebraic Holant.Complexity
namespace A
export EOBinaryPlaneIsingAccess (source output)
end A
namespace G
export EOBinaryPlaneIsingGadget (p q output_table)
end G
namespace P
export EOBinaryPlanePositive (Good)
end P
namespace N
export BinaryCSPProgrammeNative (targetValue target_semantics)
end N
namespace V
export RealDenseSignTwistStageAccess (value)
end V
namespace S
export BinaryIsingSource (positiveControlled)
end S
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (f : Signature K 2)

def realP (g : Signature ℝ 2) : ℝ := g ![false,false]*g ![true,true]
def realQ (g : Signature ℝ 2) : ℝ := g ![false,true]*g ![true,false]
def ratio (g : Signature ℝ 2) : ℝ := realQ g/realP g

omit [Algebra ℚ K] in
theorem parameters (into : K→+*ℂ) (g : Signature ℝ 2) (hg : P.Good g)
    (hi : ∀z,into (f z)=(g z : ℂ)) :
    G.p f≠0 ∧ G.q f≠0 ∧ 0<ratio g ∧ ratio g≠1 ∧ into (G.q f/G.p f)=(ratio g : ℂ) := by
  have hp : 0<realP g := mul_pos (hg.1 _) (hg.1 _)
  have hq : 0<realQ g := mul_pos (hg.1 _) (hg.1 _)
  have hpMap : into (G.p f)=(realP g : ℂ) := by simp only [G.p,realP,map_mul,hi,Complex.ofReal_mul]
  have hqMap : into (G.q f)=(realQ g : ℂ) := by simp only [G.q,realQ,map_mul,hi,Complex.ofReal_mul]
  have hp0 : G.p f≠0 := by
    intro hz
    have hh := congrArg into hz
    rw [hpMap,map_zero] at hh
    exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hp)) hh
  have hq0 : G.q f≠0 := by
    intro hz
    have hh := congrArg into hz
    rw [hqMap,map_zero] at hh
    exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hq)) hh
  refine ⟨hp0,hq0,div_pos hq hp,?_,?_⟩
  · intro he
    have heq : realQ g=realP g := (div_eq_one_iff_eq (ne_of_gt hp)).mp he
    have hd : 0<realP g-realQ g := hg.2
    linarith
  · rw [map_div₀,hqMap,hpMap]
    exact (Complex.ofReal_div _ _).symm

theorem native_eq (M : Signature K 4) : N.targetValue F M=V.value M := by
  funext r
  exact N.target_semantics F M r

def nativeAccess : LengthControlledOracleReduction ExactTwoChainQueries.targetEncoding F.encoding
    ExactTwoChainQueries.targetEncoding F.encoding (N.targetValue F (A.output f))
      (N.targetValue F (EOBinaryPlaneCore.lift f)) := by
  rw [native_eq,native_eq]
  exact A.source F f

/-- Complete finite-machine source for a table whose named complex image is
positive and has strictly positive determinant. No Ising access premise remains. -/
def controlled (into : K→+*ℂ) (g : Signature ℝ 2) (hg : P.Good g)
    (hi : ∀z,into (f z)=(g z : ℂ)) :
    LengthControlledOracleReduction BinaryCSPProgrammeValidated.inputEncoding F.encoding
      ExactTwoChainQueries.targetEncoding F.encoding (BinaryCSPProgrammeSigned.targetValue (K:=K))
        (N.targetValue F (EOBinaryPlaneCore.lift f)) := by
  obtain ⟨hp,hq,hr,hne,hratio⟩ := parameters f into g hg hi
  have hm : A.output f=EOBinaryPlaneCore.lift (BinaryIsingWeights.table (G.p f) (G.q f)) :=
    congrArg EOBinaryPlaneCore.lift (G.output_table f)
  exact C.composeControlled
    (S.positiveControlled F (A.output f) (G.p f) (G.q f) hm hp hq into (ratio g) hr hne hratio)
    (nativeAccess F f)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositiveSource
