import Holant.Complexity.FixedFieldMachines.Concrete
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.SimpleRing.Basic


namespace Holant.LocalDrafts.MainChain.FieldCodec
open Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open scoped BigOperators
noncomputable section

def matrixValue {n m : ℕ} (A : Fin m → Fin n → ℚ) (v : Fin n → ℚ) : Fin m → ℚ :=
  fun j => ∑ i, A j i * v i

/-- Fixed-dimensional matrix multiplication built from counted rational
arithmetic, physical input copying, coordinate parsing and serialization. -/
def matrixComputes {n m : ℕ} (A : Fin m → Fin n → ℚ) :
    Computes (vectorEncoding n) (vectorEncoding m) (matrixValue A) := by
  apply assembleComputes
  intro j
  exact Concrete.rationalProvider.sumComputes (vectorEncoding n) n
    (fun v i => A j i * v i)
    (fun i => Concrete.rationalProvider.mulComputes
      (constantComputes (vectorEncoding n) rationalEncoding (A j i))
      (coordinateComputes n i))

variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
    {n m : ℕ} (F : FixedField K n) (G : FixedField L m) (φ : K →ₗ[ℚ] L)

def coordinateMatrix : Fin m → Fin n → ℚ :=
  fun j i => G.decode.symm (φ (F.basis i)) j

theorem matrix_correct (v : Fin n → ℚ) :
    matrixValue (coordinateMatrix F G φ) v = G.decode.symm (φ (F.decode v)) := by
  rw [show F.decode v = ∑ i, v i • F.basis i from F.basis.equivFun_symm_apply v]
  funext j
  simp only [matrixValue, coordinateMatrix, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- No input carries a basis-conversion certificate, and the runtime machine
does not evaluate the semantic map φ as an unbounded primitive. -/
def computes : Computes F.encoding G.encoding φ := by
  apply recode (matrixComputes (coordinateMatrix F G φ)) F.decode.symm (fun _ => rfl)
  intro x
  change (vectorEncoding m).encode
      (matrixValue (coordinateMatrix F G φ) (F.decode.symm x)) =
    (vectorEncoding m).encode (G.decode.symm (φ x))
  rw [matrix_correct, LinearEquiv.apply_symm_apply]

def outputBound : PolynomialOutputBound F.encoding G.encoding φ :=
  (computes F G φ).outputBound

def basisChange {k : ℕ} (F' : FixedField K k) :
    Computes F.encoding F'.encoding (id : K → K) :=
  computes F F' LinearMap.id

/-- A total linear retraction has fixed rational coordinates.  On answers in
the embedded field it recovers the original value exactly.  No membership test
or supplied inverse algorithm is required. -/
def retractComputes (φ : K →ₐ[ℚ] L) :
    Computes G.encoding F.encoding φ.toLinearMap.leftInverse :=
  computes G F φ.toLinearMap.leftInverse

theorem retract_embedding (φ : K →ₐ[ℚ] L) (x : K) :
    φ.toLinearMap.leftInverse (φ x) = x :=
  LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr φ.toRingHom.injective) x

end
end Holant.LocalDrafts.MainChain.FieldCodec
