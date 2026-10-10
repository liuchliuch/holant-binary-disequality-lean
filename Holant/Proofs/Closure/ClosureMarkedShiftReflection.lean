import Holant.Proofs.Closure.ClosureMarkedDihedralA0

/-! NEW POST-RECOVERY SOURCE; fresh strict verification is required.
Internally select an actual ORIGINAL-field reflection in the native-X
noncyclic branch. The Hadamard coordinates lie in L and its nonzero multiplier
and reflection phase are literal entry ratios in L. No model/phase selector,
new field extraction, coordinate oracle or target compiler is input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]

def reflection (t : L) : Binary (K:=L) :=
  Matrix.of (fun a b => if a = b then 0 else (if a then 1 else t))

def frozenTransfer (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (j : completeGroup F hτ) : Matrix.GeneralLinearGroup Bool L :=
  ClosureMarkedDihedralCoordinates.Source.actualTransferGL F
    (actualRepresentative F hτ j) (actualRepresentative_actual F hτ j)

theorem frozenTransfer_class (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (j : completeGroup F hτ) : pglMk L (frozenTransfer F hτ j) = j.val := by
  apply pglToProjectiveClass_injective
  rw [pglToProjectiveClass_mk]
  exact actualRepresentative_class F hτ j

def normalizedTransfer (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (j : completeGroup F hτ) : Matrix.GeneralLinearGroup Bool L :=
  ClosureMarkedCyclic.Source.sourceNormalize (frozenTransfer F hτ j)

theorem normalizedTransfer_class (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (j : completeGroup F hτ) :
    pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) (normalizedTransfer F hτ j)) =
      ClosureMarkedCyclic.normalize (pglExtend (complexEmbedding φ) j.val) := by
  rw [normalizedTransfer,ClosureMarkedCyclic.Source.sourceNormalize_class]
  rw [← pglExtend_mk,frozenTransfer_class]

/-- Reflection coefficients are recovered from the SAME normalized source
matrix. Nonsingularity supplies both nonzero pivots; no scalar is erased. -/
theorem antidiagonal_ratio (W : Matrix.GeneralLinearGroup Bool L)
    (h00 : W false false = 0) (h11 : W true true = 0) :
    ∃ c t : L, c ≠ 0 ∧ t ≠ 0 ∧ (W : Binary (K:=L)) = c • reflection t := by
  have h0 := congrArg (fun M : Binary (K:=L) => M false false) W.val_inv
  have h1 := congrArg (fun M : Binary (K:=L) => M true true) W.val_inv
  simp [Matrix.mul_apply,h00,h11] at h0 h1
  have h01 : W false true ≠ 0 := by intro hz; simp [hz] at h0
  have h10 : W true false ≠ 0 := by intro hz; simp [hz] at h1
  refine ⟨W true false,W false true / W true false,h10,div_ne_zero h01 h10,?_⟩
  ext a b
  cases a <;> cases b <;>
    simp [reflection,h00,h11,h10,div_eq_mul_inv,mul_comm,mul_left_comm]

/-- Closed source selection from the genuine finite noncyclic complete group.
The noncyclic and native-axis hypotheses are actual local routing branches;
they are not a desired model or successful future classification certificate. -/
theorem exists_reflection (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (hnc : ¬ IsCyclic (group φ F hτ)) :
    ∃ j : completeGroup F hτ, ∃ c t : L, c ≠ 0 ∧ t ≠ 0 ∧
      (normalizedTransfer F hτ j : Binary (K:=L)) = c • reflection t ∧
      pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ)
        (normalizedTransfer F hτ j)) ∉ diagonalTorus := by
  let H := group φ F hτ
  let H0 := ClosureMarkedCyclic.normalized H
  letI : Finite H := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  let e := H.equivMapOfInjective ClosureMarkedCyclic.normalize.toMonoidHom
    ClosureMarkedCyclic.normalize.injective
  letI : Finite H0 := Finite.of_equiv H e.toEquiv
  have hnc0 : ¬ IsCyclic H0 := by
    intro hc
    letI : IsCyclic (H.map ClosureMarkedCyclic.normalize.toMonoidHom) := hc
    exact hnc (isCyclic_of_surjective e.symm e.symm.surjective)
  have haxis : H0 ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) :=
    ClosureMarkedDihedralA0.normalized_centralizer H hX
  have hnot : ¬ H0 ≤ diagonalTorus :=
    fun ht => hnc0 (finite_diagonal_subgroup_isCyclic H0 ht)
  obtain ⟨q,hq,hqT⟩ := Set.not_subset.mp hnot
  have hqin : q ∈ H0 := hq
  obtain ⟨r,hr,hrq⟩ := hq
  change r ∈ completeGroup
    (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily (complexEmbedding φ) F)
    (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ) at hr
  rw [ClosureFieldBridgeGroups.completeGroup_image (complexEmbedding φ) F hτ] at hr
  obtain ⟨j,hj,hjr⟩ := hr
  let key : completeGroup F hτ := ⟨j,hj⟩
  let W := normalizedTransfer F hτ key
  have hw : pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) W) = q := by
    rw [normalizedTransfer_class,hjr]
    exact hrq
  have hc : Commute (pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) W)) zClass := by
    rw [hw]
    exact Subgroup.mem_centralizer_singleton_iff.mp (haxis hqin)
  have hanti : W false false = 0 ∧ W true true = 0 := by
    rcases (commute_z_iff_entries _).mp hc with hd | ha
    · obtain ⟨a,b,he⟩ := diagonal_form _ hd.1 hd.2
      have ht : q ∈ diagonalTorus := by
        rw [← hw,he,diagonal_normalize]
        exact ⟨a*b⁻¹,rfl⟩
      exact False.elim (hqT ht)
    · constructor
      · apply (complexEmbedding φ).injective
        simpa using ha.1
      · apply (complexEmbedding φ).injective
        simpa using ha.2
  obtain ⟨c,t,hc,ht,hl⟩ := antidiagonal_ratio W hanti.1 hanti.2
  exact ⟨key,c,t,hc,ht,hl,by rwa [hw]⟩

structure Reflection (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) where
  key : completeGroup F hτ
  multiplier : L
  phase : L
  multiplier_nonzero : multiplier ≠ 0
  phase_nonzero : phase ≠ 0
  literal : (normalizedTransfer F hτ key : Binary (K:=L)) = multiplier • reflection phase
  off_torus : pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ)
    (normalizedTransfer F hτ key)) ∉ diagonalTorus
  actual : ActualNonsingular F (actualRepresentative F hτ key)

def select (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (hnc : ¬ IsCyclic (group φ F hτ)) : Reflection φ F hτ := by
  let receipt := exists_reflection φ F hτ hX hnc
  let key := Classical.choose receipt
  let c := Classical.choose (Classical.choose_spec receipt)
  let t := Classical.choose (Classical.choose_spec (Classical.choose_spec receipt))
  have h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec receipt))
  exact ⟨key,c,t,h.1,h.2.1,h.2.2.1,h.2.2.2,actualRepresentative_actual F hτ key⟩

/-- The universal actual-Z normalizer becomes an X normalizer under the
SAME Hadamard change. X is a semantic mark here, not a newly retained gadget. -/
theorem normalized_normalizerX (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) :
    xClass ∈ Subgroup.normalizer (ClosureMarkedCyclic.normalized (group φ F hτ) : Set (PGL2 ℂ)) := by
  have hz := ClosureMarkedReversalOvergroup.Ambient.actual_normalizedZ φ F hτ
  have h := Subgroup.le_normalizer_map (H:=group φ F hτ)
    ClosureMarkedCyclic.normalize.toMonoidHom
    (show ClosureMarkedCyclic.normalize zClass ∈
      (Subgroup.normalizer (group φ F hτ : Set (PGL2 ℂ))).map
        ClosureMarkedCyclic.normalize.toMonoidHom from ⟨zClass,hz,rfl⟩)
  rwa [ClosureMarkedDihedralA0.nativeZ_to_X] at h

namespace Reflection
variable {φ : L →+* Scalar} {F : SignatureFamily L} {hτ : ResidualTorsion F}
variable (R : Reflection φ F hτ)

def phaseUnit : ℂˣ := Units.mk0 (complexEmbedding φ R.phase)
  ((map_ne_zero (complexEmbedding φ)).mpr R.phase_nonzero)

theorem class_eq :
    pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ)
      (normalizedTransfer F hτ R.key)) = torusHom R.phaseUnit * xClass := by
  have hf : pglMk ℂ (antidiagonalGL R.phaseUnit 1) = torusHom R.phaseUnit * xClass := by
    simpa only [inv_one,mul_one] using antidiagonal_factor R.phaseUnit 1
  rw [← hf]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨complexEmbedding φ R.multiplier,
    (map_ne_zero (complexEmbedding φ)).mpr R.multiplier_nonzero,?_⟩
  change Matrix.map (normalizedTransfer F hτ R.key : Binary (K:=L)) (complexEmbedding φ) = _
  rw [R.literal,Matrix.map_smul' (complexEmbedding φ) R.multiplier _ (complexEmbedding φ).map_mul]
  ext a b
  cases a <;> cases b <;>
    simp [reflection,phaseUnit,antidiagonalGL,antidiagonal]

theorem member :
    pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ)
      (normalizedTransfer F hτ R.key)) ∈ ClosureMarkedCyclic.normalized (group φ F hτ) := by
  rw [normalizedTransfer_class]
  refine ⟨pglExtend (complexEmbedding φ) R.key.val,?_,rfl⟩
  change pglExtend (complexEmbedding φ) R.key.val ∈ completeGroup
    (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily (complexEmbedding φ) F)
    (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ)
  rw [ClosureFieldBridgeGroups.completeGroup_image (complexEmbedding φ) F hτ]
  exact ⟨R.key.val,R.key.property,rfl⟩

def rotations (_R : Reflection φ F hτ) : Subgroup (PGL2 ℂ) :=
  ClosureMarkedCyclic.normalized (group φ F hτ) ⊓ diagonalTorus

/-- Reversal forces the selected reflection phase's SQUARE into the actual
rotation subgroup. This uses the SAME actual key, never an assumed phase deck. -/
theorem square_member : torusHom (R.phaseUnit^2) ∈ R.rotations := by
  let H0 := ClosureMarkedCyclic.normalized (group φ F hτ)
  let q := pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ)
    (normalizedTransfer F hτ R.key))
  have hq : q ∈ H0 := R.member
  have hn := (Subgroup.mem_normalizer_iff.mp (normalized_normalizerX φ F hτ) q).mp hq
  have hprod := H0.mul_mem hq hn
  have hxx : xClass*xClass = 1 := by simpa only [pow_two] using xClass_square
  have hxinv : xClass⁻¹ = xClass := inv_eq_of_mul_eq_one_right hxx
  have he : q * (xClass*q*xClass⁻¹) = torusHom (R.phaseUnit^2) := by
    dsimp only [q]
    rw [R.class_eq,hxinv]
    calc
      _ = torusHom R.phaseUnit * (xClass*xClass) * torusHom R.phaseUnit * (xClass*xClass) := by group
      _ = torusHom R.phaseUnit * torusHom R.phaseUnit := by rw [hxx]; simp
      _ = torusHom (R.phaseUnit^2) := by rw [pow_two,map_mul]
  rw [he] at hprod
  exact ⟨hprod,⟨R.phaseUnit^2,rfl⟩⟩

/-- The 2m-root condition is derived in ORIGINAL L from actual reversal and
the actual finite rotation subgroup. No replacement field or root selector is input. -/
theorem phase_twice_rotation_card : R.phase^(2*Nat.card R.rotations) = 1 := by
  let H := group φ F hτ
  let H0 := ClosureMarkedCyclic.normalized H
  letI : Finite H := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  let e := H.equivMapOfInjective ClosureMarkedCyclic.normalize.toMonoidHom
    ClosureMarkedCyclic.normalize.injective
  letI : Finite H0 := Finite.of_equiv H e.toEquiv
  letI : Finite R.rotations := Finite.of_injective
    (Subgroup.inclusion (show R.rotations ≤ H0 from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hp := congrArg Subtype.val
    (pow_card_eq_one' (x:=(⟨torusHom (R.phaseUnit^2),R.square_member⟩ : R.rotations)))
  change torusHom (R.phaseUnit^2) ^ Nat.card R.rotations = 1 at hp
  rw [← map_pow,← map_one torusHom] at hp
  have hu := congrArg Units.val (torusHom_injective hp)
  apply (complexEmbedding φ).injective
  rw [map_pow,map_one]
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,phaseUnit,Units.val_mk0,← pow_mul] using hu

/-- Every m-th root class belongs to the ACTUAL finite rotation subgroup;
its displayed cyclic model is internally selected from that subgroup. -/
theorem torus_root_member (K : Subgroup (PGL2 ℂ)) [Finite K]
    (hK : K ≤ diagonalTorus) (a : ℂˣ) (ha : a^Nat.card K = 1) : torusHom a ∈ K := by
  obtain ⟨ω,hω,hmodel⟩ := finite_torus_subgroup_eq_cyclicModel K hK
  have hm : 0 < Nat.card K := Nat.card_pos
  letI : NeZero (Nat.card K) := ⟨Nat.ne_zero_of_lt hm⟩
  have hai : (a⁻¹ : ℂˣ)^Nat.card K = 1 := by rw [inv_pow,ha,inv_one]
  have hroot : a⁻¹ ∈ rootsOfUnity (Nat.card K) ℂ := by
    apply (mem_rootsOfUnity' _ _).mpr
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val hai
  obtain ⟨k,hk,he⟩ := hω.eq_pow_of_mem_rootsOfUnity hroot
  have ht : torusHom a = pglMk ℂ (diagonalGL 1 a⁻¹) := by
    rw [diagonal_normalize]
    simp
  rw [hmodel,mem_cyclicModel_iff hm hω,ht]
  exact ⟨k,hk,by rw [he]⟩

/-- The genuine absence of actual native Z separates the SHIFTED reflection
phase from the unshifted A0 case. Its m-nonroot statement is in ORIGINAL L. -/
theorem phase_not_rotation_root (hZ : zClass ∉ group φ F hτ) :
    R.phase^Nat.card R.rotations ≠ 1 := by
  intro hphase
  let H := group φ F hτ
  let H0 := ClosureMarkedCyclic.normalized H
  letI : Finite H := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  let e := H.equivMapOfInjective ClosureMarkedCyclic.normalize.toMonoidHom
    ClosureMarkedCyclic.normalize.injective
  letI : Finite H0 := Finite.of_equiv H e.toEquiv
  letI : Finite R.rotations := Finite.of_injective
    (Subgroup.inclusion (show R.rotations ≤ H0 from inf_le_left))
    (Subgroup.inclusion_injective _)
  have hu : R.phaseUnit^Nat.card R.rotations = 1 := by
    apply Units.ext
    change (complexEmbedding φ R.phase)^Nat.card R.rotations = 1
    rw [← map_pow,hphase,map_one]
  have ht := torus_root_member R.rotations inf_le_right R.phaseUnit hu
  have hx : xClass ∈ H0 := by
    have h := H0.mul_mem (H0.inv_mem ht.1) R.member
    rw [R.class_eq] at h
    simpa only [← mul_assoc,inv_mul_cancel,one_mul] using h
  obtain ⟨r,hr,he⟩ := hx
  have hz : r = zClass := ClosureMarkedCyclic.normalize.injective
    (he.trans ClosureMarkedDihedralA0.nativeZ_to_X.symm)
  exact hZ (hz ▸ hr)

end Reflection

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection
end
