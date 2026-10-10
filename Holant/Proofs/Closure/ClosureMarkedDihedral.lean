import Holant.Proofs.Closure.ClosureFieldBridgeGroups
import Holant.Projective.FiniteSubgroupClassification.DihedralConjugacy
import Holant.Marked.Reversal

/-! A constructed marked branch, in the native coordinates.  If the actual
finite complete group centralizes the literal Z class and contains the actual
native X class, its rotation subgroup is selected and its exact reflected-torus
model is proved.  For rotation order at least three this constructs sector M
with the algebraic identity basis, preserving the SAME X edge and reversal.
No arbitrary complex conjugator is asserted to be a gadget.  Selecting this
centralizer branch from an arbitrary cyclic/dihedral group remains separate.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedral
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
namespace PC
export Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
  (diagonalGL diagonal xGL xClass zClass diagonalTorus)
end PC

abbrev inclusion : Scalar →+* ℂ := (algebraicClosure ℚ ℂ).subtype

/-- The native-coordinate model is derived without any conjugation.  Even
rotation orders one and two are retained in this theorem, rather than silently
being sent to the >=3 marked-sector interface. -/
theorem reflected_model (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : H ≤ Subgroup.centralizer ({PC.zClass} : Set (PGL2 ℂ)))
    (hx : PC.xClass ∈ H) :
    ∃ ω : ℂˣ, IsPrimitiveRoot ω (Nat.card ↥(H ⊓ PC.diagonalTorus)) ∧
      H = dihedralModel ω ∧ Nat.card H = 2 * Nat.card ↥(H ⊓ PC.diagonalTorus) := by
  let K := H ⊓ PC.diagonalTorus
  letI : Finite K := Finite.of_injective
    (Subgroup.inclusion (show K ≤ H from inf_le_left)) (Subgroup.inclusion_injective _)
  obtain ⟨ω, hω, hK⟩ := finite_torus_subgroup_eq_cyclicModel K inf_le_right
  refine ⟨ω, hω, ?_, ?_⟩
  · rw [subgroup_centralizer_eq_reflectedTorus H hH hx]
    change reflectedTorus K _ = reflectedTorus (cyclicModel ω) _
    subst K
    congr
  · calc
      Nat.card H = Nat.card ↥(reflectedTorus K inf_le_right) :=
        congrArg (fun J : Subgroup (PGL2 ℂ) => Nat.card J)
          (subgroup_centralizer_eq_reflectedTorus H hH hx)
      _ = 2 * Nat.card K := reflectedTorus_card K inf_le_right

/-- Exact residual separation: the two small reflected orders stay distinct. -/
theorem marked_range (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : H ≤ Subgroup.centralizer ({PC.zClass} : Set (PGL2 ℂ)))
    (hx : PC.xClass ∈ H) (h2 : Nat.card H ≠ 2) (h4 : Nat.card H ≠ 4) :
    3 ≤ Nat.card ↥(H ⊓ PC.diagonalTorus) := by
  let K := H ⊓ PC.diagonalTorus
  letI : Finite K := Finite.of_injective
    (Subgroup.inclusion (show K ≤ H from inf_le_left)) (Subgroup.inclusion_injective _)
  have hp : 0 < Nat.card K := Nat.card_pos
  have hc := (reflected_model H hH hx).choose_spec.2.2
  change Nat.card H = 2 * Nat.card K at hc
  change 3 ≤ Nat.card K
  omega

/-- The chosen finite-order complex root has an actual algebraic lift. -/
def liftRoot {m : ℕ} (hm : 0 < m) (ω : ℂˣ) (hω : IsPrimitiveRoot ω m) : Scalar :=
  ⟨ω, IsIntegral.of_pow hm (by
    have h : (ω : ℂ)^m = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hω.pow_eq_one
    rw [h]
    exact isIntegral_one)⟩

@[simp] theorem liftRoot_coe {m : ℕ} (hm : 0 < m) (ω : ℂˣ)
    (hω : IsPrimitiveRoot ω m) :
    inclusion (liftRoot hm ω hω) = (ω : ℂ) := rfl

theorem liftRoot_root {m : ℕ} (hm : 0 < m) (ω : ℂˣ)
    (hω : IsPrimitiveRoot ω m) : Roots m (liftRoot hm ω hω) := by
  apply Subtype.ext
  change (ω : ℂ)^m = 1
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hω.pow_eq_one

theorem R_ne_zero (t : Scalar) : (R t : Binary (K:=Scalar)) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h false) false
  simpa [R,diagonalKernel] using h00

theorem S_ne_zero (t : Scalar) : (S t : Binary (K:=Scalar)) ≠ 0 := by
  intro h
  have h10 := congrFun (congrFun h true) false
  simpa [S,R,diagonalKernel,Kernel.mul_apply,Signature.disequality] using h10

theorem map_R_pow {m : ℕ} (hm : 0 < m) (ω : ℂˣ) (hω : IsPrimitiveRoot ω m)
    (k : ℕ) :
    Matrix.map (R ((liftRoot hm ω hω)^k)) inclusion =
      (PC.diagonalGL 1 (ω^k) : Matrix Bool Bool ℂ) := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.map_apply,R,diagonalKernel,PC.diagonalGL,PC.diagonal,liftRoot,inclusion] <;> rfl

theorem map_S_pow {m : ℕ} (hm : 0 < m) (ω : ℂˣ) (hω : IsPrimitiveRoot ω m)
    (k : ℕ) :
    Matrix.map (S ((liftRoot hm ω hω)^k)) inclusion =
      (PC.xGL * PC.diagonalGL 1 (ω^k) : Matrix.GeneralLinearGroup Bool ℂ) := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.map_apply,S,R,diagonalKernel,Kernel.mul_apply,Signature.disequality,
      PC.xGL,antidiagonalGL,antidiagonal,PC.diagonalGL,PC.diagonal,
      Matrix.mul_apply,liftRoot,inclusion] <;> rfl

/-- Ambient class membership yields an ORIGINAL algebraic nonzero scalar and
an ordered literal representative, by faithful scalar descent. -/
theorem matrix_in_groupM {H : Subgroup (PGL2 ℂ)} {m : ℕ}
    (hm : 0 < m) (ω : ℂˣ) (hω : IsPrimitiveRoot ω m) (hmodel : H = dihedralModel ω)
    (U : Matrix.GeneralLinearGroup Bool Scalar)
    (hU : pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion U) ∈ H) :
    (U : Binary (K:=Scalar)) ∈ groupM m := by
  rw [hmodel,mem_dihedralModel_iff hm hω] at hU
  rcases hU with ⟨k,hk,he⟩ | ⟨k,hk,he⟩
  · refine ⟨(liftRoot hm ω hω)^k, ?_, Or.inl ?_⟩
    · unfold Roots
      rw [← pow_mul, Nat.mul_comm, pow_mul, liftRoot_root hm ω hω]
      exact one_pow _
    · have hp := pglMk_eq_iff_projectiveClass_eq.mp he
      rw [← map_R_pow hm ω hω k] at hp
      have hs := projectiveClass_map_injective inclusion (R_ne_zero ((liftRoot hm ω hω)^k)) hp
      obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp hs
      exact ⟨c,hc,he⟩
  · refine ⟨(liftRoot hm ω hω)^k, ?_, Or.inr ?_⟩
    · unfold Roots
      rw [← pow_mul, Nat.mul_comm, pow_mul, liftRoot_root hm ω hω]
      exact one_pow _
    · have hp := pglMk_eq_iff_projectiveClass_eq.mp he
      rw [← map_S_pow hm ω hω k] at hp
      have hs := projectiveClass_map_injective inclusion (S_ne_zero ((liftRoot hm ω hω)^k)) hp
      obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp hs
      exact ⟨c,hc,he⟩

/-- Constructed sector data. Its parameter, algebraic root, actual group
identity, native edge and reversal come from the given real group branch. -/
structure NativeM (H : Subgroup (PGL2 ℂ)) where
  m : ℕ
  range : 3 ≤ m
  omega : ℂˣ
  primitive : IsPrimitiveRoot omega m
  model : H = dihedralModel omega
  cardinal : Nat.card H = 2*m

def nativeM (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : H ≤ Subgroup.centralizer ({PC.zClass} : Set (PGL2 ℂ)))
    (hx : PC.xClass ∈ H) (h2 : Nat.card H ≠ 2) (h4 : Nat.card H ≠ 4) : NativeM H := by
  let spec := reflected_model H hH hx
  let ω := Classical.choose spec
  have hw := Classical.choose_spec spec
  exact ⟨Nat.card ↥(H ⊓ PC.diagonalTorus),marked_range H hH hx h2 h4,ω,hw.1,hw.2.1,hw.2.2⟩

namespace NativeM
variable {H : Subgroup (PGL2 ℂ)} (N : NativeM H)
def parameters : Parameters N.m := .M N.range

theorem same_edge : sectorEdge N.parameters.basis = Signature.disequality := edgeM

theorem same_binary (B : Holant.Marked.Mat) : transport N.parameters.basis B = B := by
  simp [parameters,Parameters.basis,transport,InvertibleKernel.identity]

theorem same_reversal (B : Holant.Marked.Mat) :
    transport N.parameters.basis (Kernel.transpose B) = Kernel.transpose B := N.same_binary _

theorem ordered_transfer (U : Matrix.GeneralLinearGroup Bool Scalar)
    (hU : pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion U) ∈ H) :
    (U : Binary (K:=Scalar)) ∈ groupM N.m :=
  matrix_in_groupM (by have := N.range; omega) N.omega N.primitive N.model U hU

end NativeM

def standard (p : Bool) (t : Scalar) : Holant.Marked.Mat := if p then S t else R t

def phaseGL {m : ℕ} (hm : 0 < m) (p : Bool) (t : Scalar) (ht : Roots m t) :
    Matrix.GeneralLinearGroup Bool ℂ :=
  let u := Units.mk0 (inclusion t) ((map_ne_zero inclusion).mpr (ht.ne_zero hm))
  if p then PC.xGL * PC.diagonalGL 1 u else PC.diagonalGL 1 u

theorem phaseGL_matrix {m : ℕ} (hm : 0 < m) (p : Bool) (t : Scalar) (ht : Roots m t) :
    (phaseGL hm p t ht : Matrix Bool Bool ℂ) = Matrix.map (standard p t) inclusion := by
  apply Matrix.ext
  intro a b
  cases p <;> cases a <;> cases b <;>
    simp [phaseGL,standard,PC.xGL,antidiagonalGL,antidiagonal,
      PC.diagonalGL,PC.diagonal,Matrix.mul_apply,R,S,Kernel.mul_apply,
      Signature.disequality,diagonalKernel]

theorem phaseClass_mem {H : Subgroup (PGL2 ℂ)} (N : NativeM H)
    (p : Bool) (t : Scalar) (ht : Roots N.m t) :
    pglMk ℂ (phaseGL (by have := N.range; omega) p t ht) ∈ H := by
  have hm : 0 < N.m := by have := N.range; omega
  letI : NeZero N.m := ⟨Nat.ne_zero_of_lt hm⟩
  let u := Units.mk0 (inclusion t) ((map_ne_zero inclusion).mpr (ht.ne_zero hm))
  have hu : u ^ N.m = 1 := by
    apply Units.ext
    change (inclusion t)^N.m = 1
    rw [← map_pow,ht,map_one]
  obtain ⟨k,hk,he⟩ := N.primitive.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity' N.m u).mpr
    (by simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val hu))
  have hmem : pglMk ℂ (phaseGL hm p t ht) ∈ dihedralModel N.omega := by
    rw [mem_dihedralModel_iff hm N.primitive]
    cases p
    · left
      exact ⟨k,hk,by change pglMk ℂ (PC.diagonalGL 1 u) = _; rw [he]⟩
    · right
      exact ⟨k,hk,by change pglMk ℂ (PC.xGL * PC.diagonalGL 1 u) = _; rw [he]⟩
  have he := congrArg (fun J : Subgroup (PGL2 ℂ) =>
    pglMk ℂ (phaseGL hm p t ht) ∈ J) N.model
  exact Eq.mpr he hmem

namespace Source
open Holant.LocalDrafts.MainChain.RingHomRealization
variable {L : Type*} [Field L] [NumberField L]

abbrev complexEmbedding (φ : L →+* Scalar) : L →+* ℂ := inclusion.comp φ
abbrev group (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Subgroup (PGL2 ℂ) :=
  completeGroup (mapFamily (complexEmbedding φ) F)
    (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ)

/-- Retained literal equality gives the ACTUAL X transfer.  The native edge
alone only gives the identity transfer, so equality is genuinely used here. -/
theorem nativeX_mem (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F) :
    PC.xClass ∈ group φ F hτ := by
  have hi : ActualNonsingular F (Signature.equality : Binary (K:=L)) := by
    refine ⟨Gadget.realizes_of_mem F .disequality _ hI, ?_⟩
    have he : Matrix.of (Signature.equality : Bool → Bool → L) = (1 : Matrix Bool Bool L) := by
      ext a b; cases a <;> cases b <;> simp [Signature.equality,Matrix.one_apply]
    change Matrix.det (Matrix.of (Signature.equality : Bool → Bool → L)) ≠ 0
    rw [he,Matrix.det_one]
    exact one_ne_zero
  have ht : (X : Binary (K:=L)) ∈ actualTransfers F := by
    refine ⟨Signature.equality,hi,1,one_ne_zero,?_⟩
    ext a b
    cases a <;> cases b <;>
      simp [transfer,Matrix.mul_apply,Signature.equality,X,Signature.disequality]
  have hx := ClosureFieldBridgeGroups.actualTransfers_map (complexEmbedding φ) ht
  refine ⟨PC.xGL, ?_, rfl⟩
  have he : Matrix.map (X : Binary (K:=L)) (complexEmbedding φ) =
      (PC.xGL : Matrix Bool Bool ℂ) := by
    rw [ClosureFieldBridgeGroups.map_X]
    ext a b
    cases a <;> cases b <;> simp [PC.xGL,antidiagonalGL,antidiagonal,X,Signature.disequality]
  change (PC.xGL : Matrix Bool Bool ℂ) ∈ actualTransfers
    (mapFamily (complexEmbedding φ) F)
  rwa [he] at hx

/-- A closed branch factory on the current actual group, with finiteness
constructed from the unchanged original field. No complete ambient group or
normal form, coordinate basis, or group parameter is supplied by the caller. -/
def nativeM (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hZ : group φ F hτ ≤ Subgroup.centralizer ({PC.zClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    NativeM (group φ F hτ) := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  exact ClosureMarkedDihedral.nativeM _ hZ (nativeX_mem φ F hτ hI) h2 h4

theorem source_cardinal (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Nat.card (group φ F hτ) = Nat.card (completeGroup F hτ) :=
  ClosureFieldBridgeGroups.completeGroup_card (complexEmbedding φ) F hτ

/-- Every actual source binary has its original ordered transfer in the
constructed algebraic M spectrum. Its source field and scalar are preserved. -/
theorem actual_transfer (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : NativeM (group φ F hτ)) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    Matrix.map (transfer B) φ ∈ groupM N.m := by
  have hd : Matrix.det (transfer B) ≠ 0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero hB.2 det_X_ne_zero
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hd
  apply N.ordered_transfer (Matrix.GeneralLinearGroup.map φ U)
  change pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) U) ∈ group φ F hτ
  refine ⟨Matrix.GeneralLinearGroup.map (complexEmbedding φ) U, ?_, rfl⟩
  exact ClosureFieldBridgeGroups.actualTransfers_map (complexEmbedding φ)
    ⟨B,hB,1,one_ne_zero,(one_smul L _).symm⟩

theorem actual_sector_transfer (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : NativeM (group φ F hτ)) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    sectorTransfer N.parameters.basis (Matrix.map B φ) ∈ groupM N.m := by
  have he : sectorTransfer N.parameters.basis (Matrix.map B φ) = Matrix.map (transfer B) φ := by
    ext a b
    cases a <;> cases b <;>
      simp [NativeM.parameters,Parameters.basis,sectorTransfer,conjugate,
        InvertibleKernel.identity,InvertibleKernel.symm,Kernel.mul_apply,
        transfer,Matrix.map_apply,Matrix.mul_apply,X,Signature.disequality,Signature.equality]
  rw [he]
  exact actual_transfer φ F hτ N B hB

theorem actual_binary_monomial (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : NativeM (group φ F hτ)) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    IsMonomial (Matrix.map B φ) := by
  have h := N.parameters.actual_isMonomial (Matrix.map B φ)
    (sectorTransfer N.parameters.basis (Matrix.map B φ))
    (actual_sector_transfer φ F hτ N B hB) (ProjectivelyEqual.refl _)
  rwa [N.same_binary] at h

/-- Inverse spectrum coverage for EVERY ordered phase. The selected binary
is a frozen actual representative over the ORIGINAL field; only its explicit
nonzero normal-form multiplier lives in the algebraic ambient field. -/
theorem standard_source_representative (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (N : NativeM (group φ F hτ))
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (p : Bool) (t : Scalar) (ht : Roots N.m t) :
    ∃ j : completeGroup F hτ, ∃ c : Scalar, c ≠ 0 ∧
      Matrix.map (actualRepresentative F hτ j) φ = scale c (standard p t) := by
  have hm : 0 < N.m := by have := N.range; omega
  let V := phaseGL hm p t ht
  let q := pglMk ℂ (V * PC.xGL)
  have hq : q ∈ group φ F hτ := by
    change pglMk ℂ (V * PC.xGL) ∈ _
    rw [map_mul]
    exact (group φ F hτ).mul_mem (phaseClass_mem N p t ht) (nativeX_mem φ F hτ hI)
  change q ∈ completeGroup (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily
    (complexEmbedding φ) F)
    (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ) at hq
  rw [ClosureFieldBridgeGroups.completeGroup_image (complexEmbedding φ) F hτ] at hq
  obtain ⟨j,hj,he⟩ := hq
  let key : completeGroup F hτ := ⟨j,hj⟩
  let B := actualRepresentative F hτ key
  have hb := actualRepresentative_actual F hτ key
  have hd : Matrix.det (transfer B) ≠ 0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero hb.2 det_X_ne_zero
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hd
  have hj' : pglMk L U = j := by
    apply pglToProjectiveClass_injective
    rw [pglToProjectiveClass_mk]
    exact actualRepresentative_class F hτ key
  have hmap : pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) U) =
      pglMk ℂ (V * PC.xGL) := by
    rw [← pglExtend_mk,hj']
    exact he
  obtain ⟨c,hc,hcEq⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp hmap)
  have hx : (PC.xGL : Matrix Bool Bool ℂ) = (X : Binary (K:=ℂ)) := by
    ext a b
    cases a <;> cases b <;> simp [PC.xGL,antidiagonalGL,antidiagonal,X,Signature.disequality]
  have hbinary : Matrix.map B (complexEmbedding φ) =
      c • Matrix.map (standard p t) inclusion := by
    have h := congrArg (fun M : Matrix Bool Bool ℂ => M * X) hcEq
    change Matrix.map (transfer B) (complexEmbedding φ) * X =
      (c • ((V : Matrix Bool Bool ℂ) * (PC.xGL : Matrix Bool Bool ℂ))) * X at h
    rw [← ClosureFieldBridgeGroups.transfer_map] at h
    simp only [transfer,hx,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] at h
    rw [phaseGL_matrix] at h
    exact h
  have hp : projectiveClass (Matrix.map (Matrix.map B φ) inclusion) =
      projectiveClass (Matrix.map (standard p t) inclusion) :=
    projectiveClass_eq_iff.mpr ⟨c,hc,hbinary⟩
  have hn : (standard p t : Binary (K:=Scalar)) ≠ 0 := by
    cases p
    · exact R_ne_zero t
    · exact S_ne_zero t
  have hs := projectiveClass_map_injective inclusion hn hp
  obtain ⟨d,hd,he⟩ := projectiveClass_eq_iff.mp hs
  exact ⟨key,d,hd,he⟩

end Source
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedral
end
