import Holant.Complexity.BinaryInterpolation.PowerPencils
import Holant.Algebraic.OpenNetwork
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Characteristic roots are derived inside the actual algebraic complex
subfield, then interpreted back in the unchanged ambient complex matrix. -/
namespace Holant.Complexity.BinaryInterpolation.AlgebraicSource
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev EntriesAlgebraic (A : Binary (K := ℂ)) : Prop := ∀ i j, IsAlgebraic ℚ (A i j)

 theorem algebraic_eigenpair (A : Binary (K := ℂ)) (hA : EntriesAlgebraic A) :
    ∃ a b : ℂ, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ b ∧
      Matrix.trace A = a+b ∧ Matrix.det A = a*b := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  let T : Binary (K := AlgebraicComplex) := fun i j => ⟨A i j,(hA i j).isIntegral⟩
  obtain ⟨a,b,ht,hd,_,_⟩ := exists_eigenpair T
  refine ⟨a,b,a.property.isAlgebraic,b.property.isAlgebraic,?_,?_⟩
  · have h := congrArg (fun z : AlgebraicComplex => (z : ℂ)) ht
    simpa [Matrix.trace,T] using h
  · rw [det_entries] at hd ⊢
    exact congrArg (fun z : AlgebraicComplex => (z : ℂ)) hd

 theorem entries_X : EntriesAlgebraic (X : Binary (K := ℂ)) := by
  intro i j
  cases i <;> cases j <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

 theorem entries_one : EntriesAlgebraic (1 : Binary (K := ℂ)) := by
  intro i j
  cases i <;> cases j <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

 theorem entries_sub {A B : Binary (K := ℂ)} (hA : EntriesAlgebraic A)
    (hB : EntriesAlgebraic B) : EntriesAlgebraic (A-B) :=
  fun i j => ((hA i j).isIntegral.sub (hB i j).isIntegral).isAlgebraic

 theorem entries_smul {A : Binary (K := ℂ)} {c : ℂ} (hc : IsAlgebraic ℚ c)
    (hA : EntriesAlgebraic A) : EntriesAlgebraic (c • A) :=
  fun i j => (hc.isIntegral.mul (hA i j).isIntegral).isAlgebraic

 theorem entries_mul {A B : Binary (K := ℂ)} (hA : EntriesAlgebraic A)
    (hB : EntriesAlgebraic B) : EntriesAlgebraic (A*B) := by
  intro i j
  change IsAlgebraic ℚ (∑ k, A i k*B k j)
  apply IsIntegral.isAlgebraic
  apply IsIntegral.sum
  intro k _
  exact (hA i k).isIntegral.mul (hB k j).isIntegral

 theorem entries_projector {A : Binary (K := ℂ)} {a b : ℂ} (hA : EntriesAlgebraic A)
    (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) :
    EntriesAlgebraic (spectralProjector A a b) :=
  entries_smul (ha.sub hb).inv (entries_sub hA (entries_smul hb entries_one))

 theorem entries_nilpotent {A : Binary (K := ℂ)} {a : ℂ} (hA : EntriesAlgebraic A)
    (ha : IsAlgebraic ℚ a) : EntriesAlgebraic (nilpotentPart A a) :=
  entries_sub hA (entries_smul ha entries_one)

end
end Holant.Complexity.BinaryInterpolation.AlgebraicSource
