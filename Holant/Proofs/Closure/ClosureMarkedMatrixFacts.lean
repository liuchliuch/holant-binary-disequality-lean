import Holant.Projective.BoundedTorsion.PGL

/-! Pure original-field marked matrix facts, split additively from the recovered
reversal module. The existing ClosureMarkedReversal namespace/API is unchanged.
No source-family, marked model, classification or FrozenSources import is needed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversal
open Holant
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {L : Type*} [Field L]

/-- Boolean determinant formula proved by genuine simultaneous reindexing. -/
theorem det_bool (T : Binary (K:=L)) :
    Matrix.det T = T false false * T true true - T false true * T true false := by
  have h := Matrix.det_fin_two (T.submatrix finTwoEquiv finTwoEquiv)
  rw [Matrix.det_submatrix_equiv_self] at h
  simpa [Matrix.submatrix,finTwoEquiv] using h

def nativeZ : Binary (K:=L) := Matrix.of (fun a b =>
  if a = b then (if a then -1 else 1) else 0)

theorem nativeZ_square : (nativeZ : Binary (K:=L)) * nativeZ = 1 := by
  ext a b
  cases a <;> cases b <;> simp [nativeZ,Matrix.mul_apply,Matrix.one_apply]

def nativeZGL : Matrix.GeneralLinearGroup Bool L where
  val := nativeZ
  inv := nativeZ
  val_inv := nativeZ_square
  inv_val := nativeZ_square

def nativeZClass : PGL2 L := pglMk L nativeZGL

theorem nativeZGL_square : (nativeZGL : Matrix.GeneralLinearGroup Bool L)^2 = 1 := by
  apply Units.ext
  simpa only [pow_two,Units.val_mul,Units.val_one,nativeZGL] using (nativeZ_square (L:=L))

theorem nativeZClass_square : (nativeZClass : PGL2 L)^2 = 1 := by
  rw [nativeZClass,← map_pow,nativeZGL_square (L:=L),map_one]

theorem nativeZClass_inv : (nativeZClass : PGL2 L)⁻¹ = nativeZClass := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using (nativeZClass_square (L:=L))

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversal
end
