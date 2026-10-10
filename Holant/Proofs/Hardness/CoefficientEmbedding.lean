import Holant.Proofs.Reductions.EightVertexNonexception.Coefficients
import Holant.Tractable.Scalars
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Literal sparse coefficient predicates commute with faithful field
embedding. A fixed ambient embedding of a number field is obtained internally;
no computability claim is made for varying semantic input fields. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.CoefficientEmbedding
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
section Coefficients
variable {L : Type} [Field L] [Algebra ℚ L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (M : Signature L 4)

def mapped : Signature AlgebraicComplex 4 := fun x=>φ (M x)

theorem zero_iff (x : Fin 4 → Bool) : mapped φ M x=0 ↔ M x=0 := φ.map_eq_zero_iff

theorem even (hM : EvenSupport M) : EvenSupport (mapped φ M) :=
  fun x hx=>(zero_iff φ M x).mpr (hM x hx)

theorem sparse (hs : SparseCase M) : SparseCase (mapped φ M) := by
  simpa only [SparseCase,entries,ne_eq,zero_iff] using hs

theorem corners (hc : NonzeroCorners M) : NonzeroCorners (mapped φ M) := by
  intro hz
  apply hc
  apply φ.injective
  change φ ((entries M).a*(entries M).x)=φ (0 : L)
  rw [map_mul,map_zero]
  exact hz

end Coefficients

section NumberField
variable {L : Type} [Field L] [NumberField L]
/-- Existence of a fixed faithful embedding, before graph input is supplied. -/
def embedding : L →ₐ[ℚ] AlgebraicComplex := by
  letI : Algebra.IsAlgebraic ℚ L := NumberField.isAlgebraic L
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  exact IsAlgClosed.lift
end NumberField

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.CoefficientEmbedding
