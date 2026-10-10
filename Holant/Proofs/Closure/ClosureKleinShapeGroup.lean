import Holant.Proofs.Closure.ClosureKleinShapeMatrix
import Holant.Proofs.Closure.ClosureKleinShapeFinite
import Holant.Proofs.Closure.ClosureSourceRowsC2GroupFacts
import Holant.Proofs.Closure.ClosureMarkedReversal

/-! NEW_POST_RECOVERY kernel-checked actual native Klein-four source. Construct literal native axes from the actual noncyclic group of
order four. No SourceDeck, row classifier or desired shape is caller input. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
open Holant
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L : Type*} [Field L]

private def nativeXGL : Matrix.GeneralLinearGroup Bool L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (X : Binary (K:=L)) det_X_ne_zero

private def nativeXClass : PGL2 L := pglMk L nativeXGL

private def representativeGL (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (k : completeGroup F torsion) : Matrix.GeneralLinearGroup Bool L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer (actualRepresentative F torsion k)) (by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero (actualRepresentative_actual F torsion k).2 det_X_ne_zero)

private theorem representativeGL_class (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (k : completeGroup F torsion) : pglMk L (representativeGL F torsion k) = k.val := by
  apply pglToProjectiveClass_injective
  exact actualRepresentative_class F torsion k

private theorem nativeX_marked (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) : (ClosureSourceRows.markedKey F torsion hI).val = nativeXClass := rfl

private theorem nativeZ_fix_X :
    ClosureMarkedReversal.nativeZClass * (nativeXClass : PGL2 L) * ClosureMarkedReversal.nativeZClass =
      nativeXClass := by
  rw [ClosureMarkedReversal.nativeZClass,nativeXClass,← map_mul,← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨-1,neg_ne_zero.mpr one_ne_zero,?_⟩
  ext i j
  cases i <;> cases j <;>
    simp [ClosureMarkedReversal.nativeZGL,ClosureMarkedReversal.nativeZ,nativeXGL,
      X,Signature.disequality,Matrix.mul_apply,Matrix.smul_apply]

private theorem nativeZ_conjugate_cancel (q : PGL2 L) :
    ClosureMarkedReversal.nativeZClass *
      (ClosureMarkedReversal.nativeZClass * q * ClosureMarkedReversal.nativeZClass) *
        ClosureMarkedReversal.nativeZClass = q := by
  have hz : (ClosureMarkedReversal.nativeZClass : PGL2 L) * ClosureMarkedReversal.nativeZClass = 1 := by
    simpa only [pow_two] using (ClosureMarkedReversal.nativeZClass_square (L:=L))
  calc
    _ = (ClosureMarkedReversal.nativeZClass * ClosureMarkedReversal.nativeZClass) * q *
      (ClosureMarkedReversal.nativeZClass * ClosureMarkedReversal.nativeZClass) := by group
    _ = q := by rw [hz]; simp

structure FourSource (F : SignatureFamily L) (torsion : ResidualTorsion F) (hI : RetainsIdentity F) where
  second : completeGroup F torsion
  notOne : second ≠ 1
  notNative : second ≠ ClosureSourceRows.markedKey F torsion hI
  a : L
  b : L
  nativeForm : transfer (actualRepresentative F torsion second) = axis a b
  nonsingular : Matrix.det (axis a b) ≠ 0
  shape : a*b = 0 ∨ a^2+b^2 = 0
  keyCases : ∀ k : completeGroup F torsion,
    k = 1 ∨ k = ClosureSourceRows.markedKey F torsion hI ∨
      k = second ∨ k = ClosureSourceRows.markedKey F torsion hI * second

variable [CharZero L]

/-- Actual group cardinality and noncyclicity generate the native literal
standard/exotic axis disjunction. Semantic Z normalization comes from reversal. -/
def nativeFour (F : SignatureFamily L) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
    (cardinal : Nat.card (completeGroup F torsion) = 4)
    (noncyclic : ¬ IsCyclic (completeGroup F torsion)) : FourSource F torsion hI := by
  classical
  let H := completeGroup F torsion
  letI : IsKleinFour H := kleinOfFour H cardinal noncyclic
  letI : Finite H := Nat.finite_of_card_ne_zero (by rw [cardinal]; norm_num)
  letI : Fintype H := Fintype.ofFinite H
  let x : H := ClosureSourceRows.markedKey F torsion hI
  have hx : x ≠ 1 := ClosureSourceRows.markedKey_ne_one F torsion hI
  have hcard : Fintype.card H = 4 := by rwa [← Nat.card_eq_fintype_card]
  let witness := existsSecond H hcard x
  let second : H := Classical.choose witness
  have notOne : second ≠ 1 := (Classical.choose_spec witness).1
  have notNative : second ≠ x := (Classical.choose_spec witness).2
  have keyCases : ∀ k : H, k = 1 ∨ k = x ∨ k = second ∨ k = x*second := by
    intro k
    have he : ({x*second,x,second,(1:H)} : Finset H) = Finset.univ :=
      IsKleinFour.eq_finset_univ hx notOne (Ne.symm notNative)
    have hm : k ∈ ({x*second,x,second,(1:H)} : Finset H) := by rw [he]; exact Finset.mem_univ k
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hp | hx | hs | h1
    · exact .inr (.inr (.inr hp))
    · exact .inr (.inl hx)
    · exact .inr (.inr (.inl hs))
    · exact .inl h1
  let U := representativeGL F torsion second
  let A : Binary (K:=L) := U
  have hU : pglMk L U = second.val := representativeGL_class F torsion second
  have hX : pglMk L nativeXGL = x.val := (nativeX_marked F torsion hI).symm
  have nonzero : A ≠ 0 := by
    intro he
    have hn := U.det_ne_zero
    change Matrix.det A ≠ 0 at hn
    rw [he] at hn
    simpa using hn
  have square : ∃ d : L, d ≠ 0 ∧ A*A = d • (1 : Binary (K:=L)) := by
    have hs : pglMk L (U*U) = pglMk L 1 := by
      rw [map_mul,map_one,hU]
      exact congrArg Subtype.val (IsKleinFour.mul_self second)
    exact projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp hs)
  have commutation : ∃ c : L, c ≠ 0 ∧ A*X = c • (X*A) := by
    have hc : second*x = x*second :=
      mul_comm_of_exponent_two (IsKleinFour.exponent_two (G:=H)) second x
    have hs : pglMk L (U*nativeXGL) = pglMk L (nativeXGL*U) := by
      rw [map_mul,map_mul,hU,hX]
      exact congrArg Subtype.val hc
    exact projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp hs)
  have notI : ¬ ∃ c : L, c ≠ 0 ∧ A = c • (1 : Binary (K:=L)) := by
    rintro ⟨c,hc,he⟩
    apply notOne
    apply Subtype.ext
    rw [← hU]
    change pglMk L U = pglMk L 1
    exact pglMk_eq_iff_projectiveClass_eq.mpr (projectiveClass_eq_iff.mpr ⟨c,hc,he⟩)
  have notX : ¬ ∃ c : L, c ≠ 0 ∧ A = c • X := by
    rintro ⟨c,hc,he⟩
    apply notNative
    apply Subtype.ext
    rw [← hU,← hX]
    exact pglMk_eq_iff_projectiveClass_eq.mpr (projectiveClass_eq_iff.mpr ⟨c,hc,he⟩)
  have axisExact : A = axis (A false false) (A false true) :=
    second_involution_axis A nonzero commutation square notI notX
  let zsecond : H := ⟨ClosureMarkedReversal.nativeZClass * second.val * ClosureMarkedReversal.nativeZClass,
    ClosureMarkedReversal.completeGroup_conjugateZ F torsion second.property⟩
  have znotOne : zsecond ≠ 1 := by
    intro he
    apply notOne
    apply Subtype.ext
    calc
      second.val = ClosureMarkedReversal.nativeZClass * zsecond.val * ClosureMarkedReversal.nativeZClass :=
        (nativeZ_conjugate_cancel second.val).symm
      _ = ClosureMarkedReversal.nativeZClass * 1 * ClosureMarkedReversal.nativeZClass := by rw [he]; rfl
      _ = 1 := by
        rw [mul_one]
        simpa only [pow_two] using (ClosureMarkedReversal.nativeZClass_square (L:=L))
  have znotNative : zsecond ≠ x := by
    intro he
    apply notNative
    apply Subtype.ext
    calc
      second.val = ClosureMarkedReversal.nativeZClass * zsecond.val * ClosureMarkedReversal.nativeZClass :=
        (nativeZ_conjugate_cancel second.val).symm
      _ = ClosureMarkedReversal.nativeZClass * x.val * ClosureMarkedReversal.nativeZClass := by rw [he]
      _ = x.val := by
        rw [nativeX_marked F torsion hI]
        exact nativeZ_fix_X
  have alternatives : zsecond = second ∨ zsecond = x*second := by
    rcases keyCases zsecond with h1 | hx | hs | hp
    · exact False.elim (znotOne h1)
    · exact False.elim (znotNative hx)
    · exact .inl hs
    · exact .inr hp
  have hZ : pglMk L (ClosureMarkedReversal.nativeZGL*U*ClosureMarkedReversal.nativeZGL) = zsecond.val := by
    rw [map_mul,map_mul,hU]
    rfl
  have normalization :
      (∃ c : L, c ≠ 0 ∧ ClosureMarkedReversal.nativeZ*A*ClosureMarkedReversal.nativeZ = c • A) ∨
      (∃ c : L, c ≠ 0 ∧ ClosureMarkedReversal.nativeZ*A*ClosureMarkedReversal.nativeZ = c • (X*A)) := by
    rcases alternatives with hs | hp
    · left
      have he : pglMk L (ClosureMarkedReversal.nativeZGL*U*ClosureMarkedReversal.nativeZGL) = pglMk L U :=
        hZ.trans ((congrArg Subtype.val hs).trans hU.symm)
      exact projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp he)
    · right
      have hxU : pglMk L (nativeXGL*U) = x.val*second.val := by rw [map_mul,hX,hU]
      have he : pglMk L (ClosureMarkedReversal.nativeZGL*U*ClosureMarkedReversal.nativeZGL) =
          pglMk L (nativeXGL*U) := hZ.trans ((congrArg Subtype.val hp).trans hxU.symm)
      exact projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp he)
  rw [axisExact] at normalization
  exact ⟨second,notOne,notNative,A false false,A false true,axisExact,
    by rw [← axisExact]; exact U.det_ne_zero,
    axis_normalization_cases (A false false) (A false true) normalization,keyCases⟩

/-- The exact raw binary of the selected actual key, with right native X. -/
theorem FourSource.second_raw {F : SignatureFamily L} {torsion : ResidualTorsion F}
    {hI : RetainsIdentity F} (S : FourSource F torsion hI) :
    actualRepresentative F torsion S.second = axis S.a S.b * X := by
  calc
    actualRepresentative F torsion S.second = transfer (actualRepresentative F torsion S.second) * X := by
      simp [transfer,Matrix.mul_assoc,X_mul_X]
    _ = axis S.a S.b * X := by rw [S.nativeForm]

/-- The product actual key has raw source binary proportional to NEGATIVE A,
rather than A X. The witness scalar is genuinely in the original field L. -/
theorem FourSource.product_raw {F : SignatureFamily L} {torsion : ResidualTorsion F}
    {hI : RetainsIdentity F} (S : FourSource F torsion hI) :
    ∃ d : L, d ≠ 0 ∧ actualRepresentative F torsion
      (ClosureSourceRows.markedKey F torsion hI * S.second) = d • (-(axis S.a S.b)) := by
  let q := ClosureSourceRows.markedKey F torsion hI * S.second
  have hx : pglMk L nativeXGL = (ClosureSourceRows.markedKey F torsion hI).val :=
    (nativeX_marked F torsion hI).symm
  have hp : pglMk L (nativeXGL * representativeGL F torsion S.second) = q.val := by
    rw [map_mul,hx,representativeGL_class]
    rfl
  have hc : projectiveClass (transfer (actualRepresentative F torsion q)) =
      projectiveClass (X * transfer (actualRepresentative F torsion S.second)) :=
    (actualRepresentative_class F torsion q).trans (congrArg pglToProjectiveClass hp).symm
  rw [S.nativeForm] at hc
  obtain ⟨d,hd,he⟩ := projectiveClass_eq_iff.mp hc
  have hm := congrArg (fun B : Binary (K:=L) => B*X) he
  have hl : transfer (actualRepresentative F torsion q)*X = actualRepresentative F torsion q := by
    simp [transfer,Matrix.mul_assoc,X_mul_X]
  have hr : X*axis S.a S.b*X = -(axis S.a S.b) := by
    ext u v
    cases u <;> cases v <;> simp [axis,X,Signature.disequality,Matrix.mul_apply]
  rw [hl,Matrix.smul_mul,hr] at hm
  exact ⟨d,hd,hm⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
end
