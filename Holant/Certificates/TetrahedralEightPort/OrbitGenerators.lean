import Holant.Certificates.RainbowOrbit.GroupRepresentatives

/-! The two one-port matrices used in the source orbit producer generate the
entire actual tetrahedral projective group. The words and multiplication data
are checked in Lean, including every nonzero scalar. -/
namespace Holant.Certificates.TetrahedralEightPort
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

def localGeneratorIndex (b : Bool) : Fin 12 := if b then 4 else 1

def localGenerator (b : Bool) : Matrix Bool Bool ℂ :=
  representative .tetrahedral (localGeneratorIndex b)

def generatorWordIndex : List Bool → Fin 12
  | [] => 0
  | b :: w => tetrahedralProductIndex (localGeneratorIndex b) (generatorWordIndex w)

def generatorWord : List Bool → Matrix Bool Bool ℂ
  | [] => 1
  | b :: w => localGenerator b * generatorWord w

def representativeWord : Fin 12 → List Bool :=
  ![[],[false],[true,true,false,true],[true,false,true,true],
    [true],[true,true,false],[false,true,true],[false,true,false],
    [true,false,true],[true,false],[false,true],[true,true]]

theorem representativeWord_index (i : Fin 12) :
    generatorWordIndex (representativeWord i) = i := by
  fin_cases i <;> decide +kernel

theorem generatorWord_exact (w : List Bool) :
    ∃ c : ℂ, c ≠ 0 ∧ generatorWord w =
      c • representative .tetrahedral (generatorWordIndex w) := by
  induction w with
  | nil =>
    refine ⟨1,one_ne_zero,?_⟩
    simpa [generatorWord,generatorWordIndex,identityIndex] using
      (representative_identity .tetrahedral).symm
  | cons b w ih =>
    obtain ⟨c,hc,he⟩ := ih
    let s := productScale .tetrahedral (localGeneratorIndex b) (generatorWordIndex w)
    have hs : (s : ℂ) ≠ 0 := Int.cast_ne_zero.mpr
      (raw_certificate .tetrahedral (localGeneratorIndex b) (generatorWordIndex w)).1
    refine ⟨c*s,mul_ne_zero hc hs,?_⟩
    simp only [generatorWord,he,localGenerator,Matrix.mul_smul]
    rw [mul_exact,smul_smul]
    rfl

theorem representativeWord_exact (i : Fin 12) :
    ∃ c : ℂ, c ≠ 0 ∧ generatorWord (representativeWord i) =
      c • representative .tetrahedral i := by
  simpa [representativeWord_index] using generatorWord_exact (representativeWord i)

theorem generatorWord_mem (w : List Bool) :
    groupDirection .tetrahedral (generatorWord w) := by
  obtain ⟨c,hc,he⟩ := generatorWord_exact w
  rw [he]
  exact groupDirection_smul .tetrahedral (representative_mem .tetrahedral _) hc

/-- This is equality up to an arbitrary nonzero complex scalar, rather than an
identification of the twelve enumerated indices with the source group. -/
theorem tetrahedral_generated (U : Matrix Bool Bool ℂ) :
    groupDirection .tetrahedral U ↔
      ∃ w : List Bool, ∃ c : ℂ, c ≠ 0 ∧ U = c • generatorWord w := by
  constructor
  · intro h
    obtain ⟨i,c,hc,he⟩ := (complete .tetrahedral U).mp h
    obtain ⟨d,hd,hdw⟩ := representativeWord_exact i
    refine ⟨representativeWord i,c/d,div_ne_zero hc hd,?_⟩
    rw [hdw,smul_smul,div_mul_cancel₀ _ hd]
    exact he
  · rintro ⟨w,c,hc,rfl⟩
    exact groupDirection_smul .tetrahedral (generatorWord_mem w) hc

theorem localGenerator_false : localGenerator false = Matrix.of Q1 := by
  ext a b
  cases a <;> cases b <;>
    simp [localGenerator,localGeneratorIndex,representative,raw,tetrahedralRaw,
      goldenMatrix,GoldenInt.eval,quaternion,Q0,Q1,Q2,Q3,Signature.equality]

theorem localGenerator_true : localGenerator true =
    Matrix.of Q0 + Matrix.of Q1 + Matrix.of Q2 + Matrix.of Q3 := by
  ext a b
  cases a <;> cases b <;>
    simp [localGenerator,localGeneratorIndex,representative,raw,tetrahedralRaw,
      goldenMatrix,GoldenInt.eval,quaternion,Q0,Q1,Q2,Q3,Signature.equality]

end
end Holant.Certificates.TetrahedralEightPort
