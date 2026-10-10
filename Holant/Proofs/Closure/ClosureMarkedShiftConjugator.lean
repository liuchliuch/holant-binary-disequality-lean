import Holant.Proofs.Closure.ClosureMarkedShiftReflection
import Holant.Proofs.Closure.ClosureAlgebraicSquare

/-! NEW POST-RECOVERY SOURCE; fresh strict verification is required.
An algebraic coordinate basis is internally selected from the SAME actual
original-field reflection key. Its exact transformed transfer multiplier and
native-edge matrix remain explicit. The coordinate basis is not an oracle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftConjugator
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
open ClosureMarkedShiftReflection
open ClosureMarkedCyclic (coordinateGL)
open ClosureMarkedDihedral (inclusion)
variable {L : Type*} [Field L] [NumberField L]

def scaleCoordinates (s : Scalar) (hs : s ≠ 0) : Matrix.GeneralLinearGroup Bool Scalar where
  val := Matrix.of (diagonalKernel 1 s)
  inv := Matrix.of (diagonalKernel 1 s⁻¹)
  val_inv := by
    ext a b
    cases a <;> cases b <;> simp [diagonalKernel,Matrix.mul_apply,hs]
  inv_val := by
    ext a b
    cases a <;> cases b <;> simp [diagonalKernel,Matrix.mul_apply,hs]

theorem coordinate_factor (s : Scalar) (hs : s ≠ 0) :
    coordinateGL (basisA s hs) = coordinateGL ClosureMarkedCyclic.basis * scaleCoordinates s hs := by
  apply Units.ext
  ext a b
  cases a <;> cases b <;>
    simp [coordinateGL,basisA,UA,ClosureMarkedCyclic.basis,scaleCoordinates,
      diagonalKernel,Matrix.mul_apply]

theorem normalized_factor (s : Scalar) (hs : s ≠ 0)
    (V : Matrix.GeneralLinearGroup Bool Scalar) :
    ClosureMarkedDihedralCoordinates.normalizedGL (basisA s hs) V =
      (scaleCoordinates s hs)⁻¹ *
        ClosureMarkedDihedralCoordinates.normalizedGL ClosureMarkedCyclic.basis V * scaleCoordinates s hs := by
  unfold ClosureMarkedDihedralCoordinates.normalizedGL
  rw [coordinate_factor,mul_inv_rev]
  group

theorem reflection_scaled (s eta c : Scalar) (hs : s ≠ 0) (heta : eta ≠ 0)
    (hsq : s^2 = eta⁻¹) :
    ((scaleCoordinates s hs)⁻¹ : Matrix.GeneralLinearGroup Bool Scalar).val *
      (c • reflection eta) * (scaleCoordinates s hs).val = (c/s) • X := by
  have hi : ((scaleCoordinates s hs)⁻¹ : Matrix.GeneralLinearGroup Bool Scalar).val =
      Matrix.of (diagonalKernel 1 s⁻¹) := rfl
  rw [hi,Matrix.mul_smul,Matrix.smul_mul]
  have hbase : Matrix.of (diagonalKernel 1 s⁻¹) * reflection eta *
      (scaleCoordinates s hs).val = s⁻¹ • X := by
    have hprod : eta*s^2 = 1 := by rw [hsq,mul_inv_cancel₀ heta]
    have hprodC : (eta : ℂ)*(s : ℂ)^2 = 1 := by exact_mod_cast hprod
    ext a b
    cases a <;> cases b <;>
      simp [scaleCoordinates,reflection,diagonalKernel,Matrix.mul_apply,X,Signature.disequality] <;>
      field_simp [hs] <;>
      first | linear_combination hprod | linear_combination hprodC
  rw [hbase,smul_smul]
  simp only [div_eq_mul_inv]

def coordinateUnit (s : Scalar) (hs : s ≠ 0) : ℂˣ :=
  Units.mk0 (inclusion s) ((map_ne_zero inclusion).mpr hs)

theorem scaleCoordinates_class (s : Scalar) (hs : s ≠ 0) :
    pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (scaleCoordinates s hs)) =
      torusHom (coordinateUnit s hs)⁻¹ := by
  have he : Matrix.GeneralLinearGroup.map inclusion (scaleCoordinates s hs) =
      diagonalGL 1 (coordinateUnit s hs) := by
    apply Units.ext
    ext a b
    cases a <;> cases b <;>
      simp [scaleCoordinates,coordinateUnit,diagonalGL,diagonal,diagonalKernel]
  rw [he,diagonal_normalize]
  simp

def diagonalNormalize (s : Scalar) (hs : s ≠ 0) : MulAut (PGL2 ℂ) :=
  MulAut.conj ((pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (scaleCoordinates s hs)))⁻¹)

theorem normalize_factor (s : Scalar) (hs : s ≠ 0) (q : PGL2 ℂ) :
    ClosureMarkedDihedralCoordinates.normalize (basisA s hs) q =
      diagonalNormalize s hs (ClosureMarkedCyclic.normalize q) := by
  change (pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (coordinateGL (basisA s hs))))⁻¹ * q *
    pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (coordinateGL (basisA s hs))) =
      (pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (scaleCoordinates s hs)))⁻¹ *
        ((pglMk ℂ ClosureMarkedCyclic.ambientCoordinates)⁻¹ * q *
          pglMk ℂ ClosureMarkedCyclic.ambientCoordinates) *
            pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (scaleCoordinates s hs))
  rw [coordinate_factor,map_mul,map_mul,mul_inv_rev]
  simp only [ClosureMarkedCyclic.ambientCoordinates]
  group

theorem diagonal_fix (s : Scalar) (hs : s ≠ 0) (q : PGL2 ℂ)
    (hq : q ∈ diagonalTorus) : diagonalNormalize s hs q = q := by
  obtain ⟨a,rfl⟩ := hq
  change (pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (scaleCoordinates s hs)))⁻¹ *
    torusHom a * pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (scaleCoordinates s hs)) = torusHom a
  rw [scaleCoordinates_class]
  simp only [← map_inv,← map_mul,inv_inv]
  congr 1
  simp [mul_comm,mul_left_comm,mul_assoc]

theorem diagonal_torus_map (s : Scalar) (hs : s ≠ 0) :
    diagonalTorus.map (diagonalNormalize s hs).toMonoidHom = diagonalTorus := by
  apply Subgroup.ext
  intro q
  constructor
  · rintro ⟨r,hr,rfl⟩
    change diagonalNormalize s hs r ∈ diagonalTorus
    rwa [diagonal_fix s hs r hr]
  · intro hq
    exact ⟨q,hq,diagonal_fix s hs q hq⟩

theorem normalized_group_factor (s : Scalar) (hs : s ≠ 0) (H : Subgroup (PGL2 ℂ)) :
    ClosureMarkedDihedralCoordinates.normalized (basisA s hs) H =
      (ClosureMarkedCyclic.normalized H).map (diagonalNormalize s hs).toMonoidHom := by
  unfold ClosureMarkedDihedralCoordinates.normalized ClosureMarkedCyclic.normalized
  rw [Subgroup.map_map]
  congr 1
  ext q
  exact normalize_factor s hs q

theorem normalized_rotations (s : Scalar) (hs : s ≠ 0) (H : Subgroup (PGL2 ℂ)) :
    ClosureMarkedDihedralCoordinates.normalized (basisA s hs) H ⊓ diagonalTorus =
      (ClosureMarkedCyclic.normalized H ⊓ diagonalTorus).map
        (diagonalNormalize s hs).toMonoidHom := by
  rw [normalized_group_factor,
    Subgroup.map_inf _ _ _ (diagonalNormalize s hs).injective,diagonal_torus_map]

theorem nativeX_normalized (s : Scalar) (hs : s ≠ 0) :
    ClosureMarkedDihedralCoordinates.normalize (basisA s hs) xClass = zClass := by
  rw [normalize_factor,ClosureMarkedCyclic.nativeX_to_Z]
  exact diagonal_fix s hs zClass (by rw [← torus_neg_one]; exact ⟨-1,rfl⟩)

theorem normalized_centralizer (s : Scalar) (hs : s ≠ 0) (H : Subgroup (PGL2 ℂ))
    (hX : H ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ))) :
    ClosureMarkedDihedralCoordinates.normalized (basisA s hs) H ≤
      Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
  rintro q ⟨r,hr,rfl⟩
  have hc : Commute r xClass := Subgroup.mem_centralizer_singleton_iff.mp (hX hr)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := (hc.map (ClosureMarkedDihedralCoordinates.normalize (basisA s hs)).toMonoidHom).eq
  change ClosureMarkedDihedralCoordinates.normalize (basisA s hs) r *
    ClosureMarkedDihedralCoordinates.normalize (basisA s hs) xClass =
      ClosureMarkedDihedralCoordinates.normalize (basisA s hs) xClass *
        ClosureMarkedDihedralCoordinates.normalize (basisA s hs) r at h
  rwa [nativeX_normalized] at h

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftConjugator

namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection.Reflection
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
open ClosureMarkedShiftConjugator
open ClosureMarkedDihedral (inclusion)
variable {L : Type*} [Field L] [NumberField L]
variable {φ : L →+* Scalar} {F : SignatureFamily L} {hτ : ResidualTorsion F}
variable (R : ClosureMarkedShiftReflection.Reflection φ F hτ)

def eta : Scalar := φ R.phase


theorem eta_nonzero : R.eta ≠ 0 := (map_ne_zero φ).mpr R.phase_nonzero

def square : Scalar := ClosureAlgebraicSquare.inverseRoot R.eta

theorem square_eq : R.square^2 = R.eta⁻¹ := ClosureAlgebraicSquare.inverseRoot_sq R.eta

theorem square_nonzero : R.square ≠ 0 :=
  ClosureAlgebraicSquare.inverseRoot_ne_zero R.eta R.eta_nonzero

def basis : InvertibleKernel := basisA R.square R.square_nonzero

theorem hadamard_source_map :
    ClosureMarkedDihedralCoordinates.normalizedGL ClosureMarkedCyclic.basis
      (Matrix.GeneralLinearGroup.map φ (frozenTransfer F hτ R.key)) =
        Matrix.GeneralLinearGroup.map φ (normalizedTransfer F hτ R.key) := by
  simp only [ClosureMarkedDihedralCoordinates.normalizedGL,normalizedTransfer,
    ClosureMarkedCyclic.Source.sourceNormalize,map_mul,map_inv,
    ClosureMarkedCyclic.Source.sourceCoordinates_map]

/-- The SAME chosen actual source binary is sent to a literal multiple of X.
The old pivot is still in L; the new square-root factor is recorded algebraically. -/
theorem chosen_literal :
    (ClosureMarkedDihedralCoordinates.normalizedGL R.basis
      (Matrix.GeneralLinearGroup.map φ (frozenTransfer F hτ R.key)) : Binary (K:=Scalar)) =
        (φ R.multiplier/R.square) • X := by
  rw [basis,normalized_factor,R.hadamard_source_map]
  change ((scaleCoordinates R.square R.square_nonzero)⁻¹ :
    Matrix.GeneralLinearGroup Bool Scalar).val *
      Matrix.map (normalizedTransfer F hτ R.key : Binary (K:=L)) φ *
        (scaleCoordinates R.square R.square_nonzero).val = _
  rw [R.literal,Matrix.map_smul' φ R.multiplier _ φ.map_mul]
  have hm : Matrix.map (reflection R.phase) φ = reflection R.eta := by
    ext a b
    cases a <;> cases b <;> simp [reflection,eta]
  rw [hm]
  exact reflection_scaled R.square R.eta (φ R.multiplier) R.square_nonzero R.eta_nonzero R.square_eq

theorem chosen_sector :
    sectorTransfer R.basis (Matrix.map (actualRepresentative F hτ R.key) φ) =
      scale (φ R.multiplier/R.square) Signature.disequality := by
  rw [← ClosureMarkedDihedralCoordinates.Source.actual_normalized_matrix R.basis φ F
    (actualRepresentative F hτ R.key) (actualRepresentative_actual F hτ R.key)]
  exact R.chosen_literal

theorem chosen_multiplier_nonzero : φ R.multiplier/R.square ≠ 0 :=
  div_ne_zero ((map_ne_zero φ).mpr R.multiplier_nonzero) R.square_nonzero

theorem same_edge : sectorEdge R.basis = scale 2 (diagonalKernel 1 (-R.eta⁻¹)) :=
  edgeA_eta R.square_eq

theorem same_reversal (B : Holant.Marked.Mat) :
    transport R.basis (Kernel.transpose B) = Kernel.transpose (transport R.basis B) :=
  transport_reversal R.basis B

theorem chosen_class :
    pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion
      (ClosureMarkedDihedralCoordinates.normalizedGL R.basis
        (Matrix.GeneralLinearGroup.map φ (frozenTransfer F hτ R.key)))) = xClass := by
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨inclusion (φ R.multiplier/R.square),
    (map_ne_zero inclusion).mpr R.chosen_multiplier_nonzero,?_⟩
  change Matrix.map
    (ClosureMarkedDihedralCoordinates.normalizedGL R.basis
      (Matrix.GeneralLinearGroup.map φ (frozenTransfer F hτ R.key)) : Binary (K:=Scalar)) inclusion = _
  rw [R.chosen_literal,Matrix.map_smul' inclusion (φ R.multiplier/R.square) _ inclusion.map_mul]
  ext a b
  cases a <;> cases b <;>
    simp [X,xGL,antidiagonalGL,antidiagonal,Signature.disequality]

theorem chosen_member : xClass ∈ ClosureMarkedDihedralCoordinates.normalized R.basis (group φ F hτ) := by
  have h := ClosureMarkedDihedralCoordinates.Source.actual_normalized_member R.basis φ F hτ
    (actualRepresentative F hτ R.key) (actualRepresentative_actual F hτ R.key)
  change pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion
    (ClosureMarkedDihedralCoordinates.normalizedGL R.basis
      (Matrix.GeneralLinearGroup.map φ (frozenTransfer F hτ R.key)))) ∈ _ at h
  rwa [R.chosen_class] at h

/-- The actual source group is normalized by the constructed algebraic basis.
Both complete model selection and its range are internally produced. -/
def selected (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    ClosureMarkedDihedral.NativeM (ClosureMarkedDihedralCoordinates.normalized R.basis (group φ F hτ)) := by
  let H := group φ F hτ
  let e := H.equivMapOfInjective (ClosureMarkedDihedralCoordinates.normalize R.basis).toMonoidHom
    (ClosureMarkedDihedralCoordinates.normalize R.basis).injective
  letI : Finite H := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  letI : Finite (ClosureMarkedDihedralCoordinates.normalized R.basis H) := Finite.of_equiv H e.toEquiv
  have hc : Nat.card (ClosureMarkedDihedralCoordinates.normalized R.basis H) = Nat.card H :=
    Nat.card_congr e.toEquiv.symm
  exact ClosureMarkedDihedral.nativeM _
    (normalized_centralizer R.square R.square_nonzero H hX) R.chosen_member (hc ▸ h2) (hc ▸ h4)

theorem selected_rotation_card
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    (R.selected hX h2 h4).m = Nat.card R.rotations := by
  change Nat.card ↥(ClosureMarkedDihedralCoordinates.normalized R.basis (group φ F hτ) ⊓ diagonalTorus) = _
  rw [basis,normalized_rotations]
  exact Nat.card_congr
    (R.rotations.equivMapOfInjective (diagonalNormalize R.square R.square_nonzero).toMonoidHom
      (diagonalNormalize R.square R.square_nonzero).injective).toEquiv.symm

/-- Every actual ordered source binary now lies in the internally selected
complete normalized transfer model; no binary-shape certificate is input. -/
theorem actual_sector_spectrum
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    sectorTransfer R.basis (Matrix.map B φ) ∈ groupM (R.selected hX h2 h4).m :=
  ClosureMarkedDihedralCoordinates.Source.actual_sector_spectrum R.basis φ F hτ
    (R.selected hX h2 h4) B hB

/-- The native source transfer has the constructed shifted A shape after
the source embedding. This is a statement about every actual binary, not a
supplied shape certificate or an assertion that its entries lie outside L. -/
theorem actual_native_transfer_spectrum
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    Kernel.mul (Matrix.map B φ) Signature.disequality ∈ groupA (R.selected hX h2 h4).m R.eta := by
  have h := (groupA_conjugate_iff (R.selected hX h2 h4).m R.square_nonzero
    R.eta_nonzero R.square_eq (sectorTransfer R.basis (Matrix.map B φ))).mp
      (R.actual_sector_spectrum hX h2 h4 B hB)
  change conjugate R.basis (sectorTransfer R.basis (Matrix.map B φ)) ∈ _ at h
  simpa only [sectorTransfer,conjugate_inverse'] using h

/-- Inverse phase coverage chooses a genuine source key in ORIGINAL L.
The multiplier is explicitly algebraic; no bare transformed table is relabelled. -/
theorem standard_source_representative
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (p : Bool) (t : Scalar) (ht : Roots (R.selected hX h2 h4).m t) :
    ∃ j : completeGroup F hτ, ∃ c : Scalar, c ≠ 0 ∧
      sectorTransfer R.basis (Matrix.map (actualRepresentative F hτ j) φ) =
        scale c (ClosureMarkedDihedral.standard p t) :=
  ClosureMarkedDihedralCoordinates.Source.source_sector_representative R.basis φ F hτ
    (R.selected hX h2 h4) p t ht

/-- Every normalized phase has an actual original-field binary source whose
ordered coordinate table uses the SAME marked inverse edge. Its algebraic
nonzero multiplier is kept explicitly for charged physical return. -/
theorem standard_source_table
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4)
    (p : Bool) (t : Scalar) (ht : Roots (R.selected hX h2 h4).m t) :
    ∃ j : completeGroup F hτ, ∃ c : Scalar, c ≠ 0 ∧
      transport R.basis (Matrix.map (actualRepresentative F hτ j) φ) =
        scale c (Kernel.mul (ClosureMarkedDihedral.standard p t) (sectorEdgeInverse R.basis)) := by
  obtain ⟨j,c,hc,he⟩ := R.standard_source_representative hX h2 h4 p t ht
  refine ⟨j,c,hc,?_⟩
  rw [transport_eq_transfer,he,scale_mul_left]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection.Reflection

namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftConjugator.Reflection
export Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftReflection.Reflection
  (eta eta_nonzero square square_eq square_nonzero basis hadamard_source_map chosen_literal chosen_sector chosen_multiplier_nonzero same_edge same_reversal chosen_class chosen_member selected selected_rotation_card actual_sector_spectrum actual_native_transfer_spectrum standard_source_representative standard_source_table)
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedShiftConjugator.Reflection
end
