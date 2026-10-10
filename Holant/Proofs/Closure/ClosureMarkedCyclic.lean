import Holant.Proofs.Closure.ClosureMarkedDihedral

/-! Native-X marked normalization for the actual cyclic branch of order >=3.
The algebraic Hadamard coordinate change is constructed explicitly. The same
physical X edge becomes 2 diag(1,-1); this cyclic sector is kept separate from
Parameters.A, whose shifted-reflection hypotheses do not hold here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedCyclic
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace D
export ClosureMarkedDihedral (inclusion)
end D

/-- Algebraic tensor coordinates give a genuine GL matrix; the coordinate
matrix is not claimed to be an actual source gadget. -/
def coordinateGL (U : InvertibleKernel) : Matrix.GeneralLinearGroup Bool Scalar where
  val := Matrix.of U.matrix
  inv := Matrix.of U.inverse
  val_inv := by
    apply Matrix.ext
    intro a b
    have h := congrFun (congrFun U.matrix_inverse a) b
    simpa [Matrix.mul_apply,Fintype.sum_bool,Kernel.mul_apply,Matrix.one_apply,
      Signature.equality,add_comm] using h
  inv_val := by
    apply Matrix.ext
    intro a b
    have h := congrFun (congrFun U.inverse_matrix a) b
    simpa [Matrix.mul_apply,Fintype.sum_bool,Kernel.mul_apply,Matrix.one_apply,
      Signature.equality,add_comm] using h

def basis : InvertibleKernel := basisA 1 one_ne_zero

def ambientCoordinates : Matrix.GeneralLinearGroup Bool ℂ :=
  Matrix.GeneralLinearGroup.map D.inclusion (coordinateGL basis)

def normalize : MulAut (PGL2 ℂ) := MulAut.conj ((pglMk ℂ ambientCoordinates)⁻¹)

def normalized (H : Subgroup (PGL2 ℂ)) : Subgroup (PGL2 ℂ) := H.map normalize.toMonoidHom

theorem nativeX_to_Z : normalize xClass = zClass := by
  change (pglMk ℂ ambientCoordinates)⁻¹ * pglMk ℂ xGL *
    pglMk ℂ ambientCoordinates = pglMk ℂ zGL
  rw [← map_inv,← map_mul,← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨1,one_ne_zero,?_⟩
  have hinv : ((ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Matrix Bool Bool ℂ) =
      Matrix.map (Matrix.of basis.inverse) D.inclusion := rfl
  change (ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ).val *
    xGL.val * ambientCoordinates.val = _
  rw [hinv]
  ext a b
  cases a <;> cases b <;>
    norm_num [ambientCoordinates,coordinateGL,basis,basisA,UA,UAInv,
      Matrix.mul_apply,Fintype.sum_bool,xGL,antidiagonalGL,antidiagonal,
      zGL,diagonalGL,diagonal,D.inclusion,ClosureMarkedDihedral.inclusion] <;>
    first
    | change (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1; norm_num
    | change -(2 : ℂ)⁻¹ + -(2 : ℂ)⁻¹ = -1; norm_num

/-- Cyclicity and the actual native X class construct the centralizer branch;
the centralizer relation itself is not an extra hypothesis here. -/
theorem normalized_centralizer (H : Subgroup (PGL2 ℂ)) [IsCyclic H]
    (hx : xClass ∈ H) : normalized H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
  rintro q ⟨r,hr,rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hc : Commute r xClass := by
    have h : (⟨r,hr⟩ : H) * ⟨xClass,hx⟩ = ⟨xClass,hx⟩ * ⟨r,hr⟩ := IsMulCommutative.is_comm.comm _ _
    exact congrArg Subtype.val h
  have h := (hc.map normalize.toMonoidHom).eq
  change normalize r * normalize xClass = normalize xClass * normalize r at h
  rw [nativeX_to_Z] at h
  exact h

/-- A cyclic centralizer branch of order >2 has no reflection. A generator
cannot be an antidiagonal involution, so all its powers lie in the torus. -/
theorem cyclic_centralizer_le_torus (H : Subgroup (PGL2 ℂ)) [Finite H] [IsCyclic H]
    (hH : H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)))
    (hm : 3 ≤ Nat.card H) : H ≤ diagonalTorus := by
  obtain ⟨q,hq⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hqmem : q ∈ H := hq ▸ Subgroup.mem_zpowers q
  have ho : orderOf q = Nat.card H := by rw [← hq,Nat.card_zpowers]
  have hshape : q ∈ diagonalClasses ∪ antidiagonalClasses := by
    rw [← centralizer_z]
    exact hH hqmem
  have ht : q ∈ diagonalTorus := by
    rcases hshape with hd | ⟨a,b,he⟩
    · change q ∈ (diagonalTorus : Set (PGL2 ℂ))
      rwa [diagonalTorus_carrier]
    · have hi : orderOf q = 2 := he ▸ antidiagonal_involution a b
      omega
  rw [← hq]
  exact Subgroup.zpowers_le.mpr ht

/-- The basis is algebraic and the same native physical edge is recorded with
its exact nonzero multiplier, including in this separate cyclic sector. -/
theorem same_edge : sectorEdge basis = scale 2 (diagonalKernel 1 (-1)) := by
  change Kernel.pullback Signature.disequality (UA 1) = _
  simpa using (edgeA_eta (eta:=1) (s:=1) (by simp : (1:Scalar)^2 = 1⁻¹))

theorem edge_multiplier_nonzero : (2 : Scalar) ≠ 0 := by norm_num

theorem same_reversal (B : Holant.Marked.Mat) :
    transport basis (Kernel.transpose B) = Kernel.transpose (transport basis B) :=
  transport_reversal basis B

theorem native_order_even (H : Subgroup (PGL2 ℂ)) [Finite H] (hx : xClass ∈ H) :
    Even (Nat.card H) := by
  have h := orderOf_dvd_natCard (⟨xClass,hx⟩ : H)
  rw [Subgroup.orderOf_mk,xClass_involution] at h
  exact even_iff_two_dvd.mpr h

/-- The retained X class rules out the trivial cyclic branch. The only small
residual is C2; larger cyclic groups have even order and at least four. -/
theorem native_cyclic_range (H : Subgroup (PGL2 ℂ)) [Finite H] (hx : xClass ∈ H) :
    Nat.card H = 2 ∨ 4 ≤ Nat.card H := by
  have hp : 0 < Nat.card H := Nat.card_pos
  have he := native_order_even H hx
  obtain ⟨k,hk⟩ := he
  omega

structure NativeCyclic (H : Subgroup (PGL2 ℂ)) where
  m : ℕ
  range : 3 ≤ m
  omega : ℂˣ
  primitive : IsPrimitiveRoot omega m
  model : normalized H = cyclicModel omega
  cardinal : Nat.card H = m

/-- Closed native-X cyclic factory. It chooses the root from the actual
normalized rotation subgroup, rather than accepting a normal-form witness. -/
def nativeCyclic (H : Subgroup (PGL2 ℂ)) [Finite H] [IsCyclic H]
    (hx : xClass ∈ H) (hm : 3 ≤ Nat.card H) : NativeCyclic H := by
  let e := Subgroup.equivMapOfInjective H normalize.toMonoidHom normalize.injective
  letI : Finite (normalized H) := Finite.of_equiv H e.toEquiv
  letI : IsCyclic (normalized H) := isCyclic_of_surjective e e.surjective
  have hc : Nat.card (normalized H) = Nat.card H := Nat.card_congr e.toEquiv.symm
  have ht : normalized H ≤ diagonalTorus := cyclic_centralizer_le_torus _
    (normalized_centralizer H hx) (hc ▸ hm)
  let spec := finite_torus_subgroup_eq_cyclicModel (normalized H) ht
  let ω := Classical.choose spec
  have hw := Classical.choose_spec spec
  exact ⟨Nat.card H,hm,ω,hc ▸ hw.1,hw.2,rfl⟩

namespace Source
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]

/-- The current ACTUAL cyclic complete-group branch over the ORIGINAL field.
The only retained resource premise is literal equality, used to derive X. -/
def nativeCyclic (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hc : IsCyclic (group φ F hτ)) (hm : 3 ≤ Nat.card (group φ F hτ)) :
    NativeCyclic (group φ F hτ) := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  letI := hc
  exact ClosureMarkedCyclic.nativeCyclic _ (nativeX_mem φ F hτ hI) hm

/-- The fixed Hadamard coordinates already lie in the ORIGINAL field. -/
def sourceMatrix (a b : Bool) : L := if b then (if a then -1 else 1) else 1

def sourceInverse (a b : Bool) : L :=
  if a then (if b then -(2⁻¹) else 2⁻¹) else 2⁻¹

def sourceCoordinates : Matrix.GeneralLinearGroup Bool L where
  val := Matrix.of sourceMatrix
  inv := Matrix.of sourceInverse
  val_inv := by
    ext a b
    cases a <;> cases b <;>
      norm_num [sourceMatrix,sourceInverse,Matrix.mul_apply,Fintype.sum_bool,Matrix.one_apply]
  inv_val := by
    ext a b
    cases a <;> cases b <;>
      norm_num [sourceMatrix,sourceInverse,Matrix.mul_apply,Fintype.sum_bool,Matrix.one_apply]

theorem sourceCoordinates_map (φ : L →+* Scalar) :
    Matrix.GeneralLinearGroup.map φ (sourceCoordinates (L:=L)) = coordinateGL basis := by
  apply Units.ext
  apply Matrix.ext
  intro a b
  cases a <;> cases b <;>
    simp [sourceCoordinates,sourceMatrix,coordinateGL,basis,basisA,UA]

def sourceNormalize (U : Matrix.GeneralLinearGroup Bool L) :
    Matrix.GeneralLinearGroup Bool L := sourceCoordinates⁻¹ * U * sourceCoordinates

theorem sourceNormalize_class (φ : L →+* Scalar) (U : Matrix.GeneralLinearGroup Bool L) :
    pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) (sourceNormalize U)) =
      normalize (pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) U)) := by
  have he : Matrix.GeneralLinearGroup.map (complexEmbedding φ) (sourceCoordinates (L:=L)) =
      ambientCoordinates := by
    change Matrix.GeneralLinearGroup.map D.inclusion
      (Matrix.GeneralLinearGroup.map φ sourceCoordinates) = ambientCoordinates
    rw [sourceCoordinates_map]
    rfl
  change pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) (sourceNormalize U)) =
    (pglMk ℂ ambientCoordinates)⁻¹ *
      pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) U) * pglMk ℂ ambientCoordinates
  simp only [sourceNormalize,map_mul,map_inv,he]

/-- Original-field normalized matrices map to the actual marked transfer.
Neither the coefficients nor their number field are freshly extracted. -/
theorem sourceTransfer_map (φ : L →+* Scalar) (B : Binary (K:=L)) :
    Matrix.map (((sourceCoordinates (L:=L))⁻¹ : Matrix.GeneralLinearGroup Bool L).val *
      transfer B * (sourceCoordinates (L:=L)).val) φ =
        sectorTransfer basis (Matrix.map B φ) := by
  have hi : (((sourceCoordinates (L:=L))⁻¹ : Matrix.GeneralLinearGroup Bool L) : Matrix Bool Bool L) =
      Matrix.of sourceInverse := rfl
  rw [hi]
  apply Matrix.ext
  intro a b
  cases a <;> cases b <;>
    simp [sourceCoordinates,sourceMatrix,sourceInverse,Matrix.map_apply,transfer,
      Matrix.mul_apply,Fintype.sum_bool,X,Signature.disequality,sectorTransfer,
      conjugate,basis,basisA,UA,UAInv,InvertibleKernel.symm,Kernel.mul_apply,map_ofNat,div_eq_mul_inv] <;> ring

/-- Membership in the actual normalized cyclic model for the literal
ORIGINAL-field conjugate of any actual ordered source transfer. -/
theorem source_normalized_member (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (N : NativeCyclic (group φ F hτ))
    (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    let hd : Matrix.det (transfer B) ≠ 0 :=
      (by rw [transfer,Matrix.det_mul]; exact mul_ne_zero hB.2 det_X_ne_zero)
    let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hd
    pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) (sourceNormalize U)) ∈
      cyclicModel N.omega := by
  dsimp only
  rw [← N.model,sourceNormalize_class]
  refine ⟨pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) _), ?_, rfl⟩
  refine ⟨Matrix.GeneralLinearGroup.map (complexEmbedding φ) _, ?_, rfl⟩
  exact ClosureFieldBridgeGroups.actualTransfers_map (complexEmbedding φ)
    ⟨B,hB,1,one_ne_zero,(one_smul L _).symm⟩

def rotation (t : L) : Binary (K:=L) :=
  Matrix.of (fun a b => if a = b then (if a then t else 1) else 0)

/-- The normalized transfer scalar and root are explicit ratios in the
ORIGINAL field, even though the model was selected in the ambient complex
routing group. No foreign root is installed as a source coefficient. -/
theorem cyclic_source_ratio (φ : L →+* ℂ) {m : ℕ} (hm : 0 < m)
    (ω : ℂˣ) (hω : IsPrimitiveRoot ω m) (W : Matrix.GeneralLinearGroup Bool L)
    (hW : pglMk ℂ (Matrix.GeneralLinearGroup.map φ W) ∈ cyclicModel ω) :
    ∃ c t : L, c ≠ 0 ∧ t^m = 1 ∧ (W : Binary (K:=L)) = c • rotation t := by
  obtain ⟨k,hk,he⟩ := (mem_cyclicModel_iff hm hω _).mp hW
  obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp he)
  have h00 : φ (W false false) = c := by
    simpa [diagonalGL,diagonal] using congrArg (fun M : Matrix Bool Bool ℂ => M false false) he
  have h11 : φ (W true true) = c * (ω : ℂ)^k := by
    simpa [diagonalGL,diagonal] using congrArg (fun M : Matrix Bool Bool ℂ => M true true) he
  have h01 : W false true = 0 := by
    apply φ.injective
    simpa [diagonalGL,diagonal] using congrArg (fun M : Matrix Bool Bool ℂ => M false true) he
  have h10 : W true false = 0 := by
    apply φ.injective
    simpa [diagonalGL,diagonal] using congrArg (fun M : Matrix Bool Bool ℂ => M true false) he
  have hn : W false false ≠ 0 := by
    intro h
    rw [h,map_zero] at h00
    exact hc h00.symm
  let t := W true true / W false false
  have ht : φ t = (ω : ℂ)^k := by
    dsimp [t]
    rw [map_div₀,h11,h00]
    exact mul_div_cancel_left₀ _ hc
  refine ⟨W false false,t,hn,?_,?_⟩
  · apply φ.injective
    rw [map_pow,ht,map_one,← pow_mul,Nat.mul_comm,pow_mul]
    have hw : (ω : ℂ)^m = 1 := by
      simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val hω.pow_eq_one
    rw [hw,one_pow]
  · apply Matrix.ext
    intro a b
    cases a <;> cases b <;> simp [rotation,t,h01,h10,hn,div_eq_mul_inv,mul_comm,mul_left_comm]

/-- All actual ordered binaries inherit the explicit ORIGINAL-field root
ratio through the constructed Hadamard normalization and actual model. -/
theorem actual_source_ratios (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (N : NativeCyclic (group φ F hτ))
    (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    ∃ c t : L, c ≠ 0 ∧ t^N.m = 1 ∧
      ((sourceCoordinates (L:=L))⁻¹ : Matrix.GeneralLinearGroup Bool L).val * transfer B *
        (sourceCoordinates (L:=L)).val = c • rotation t := by
  have hd : Matrix.det (transfer B) ≠ 0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero hB.2 det_X_ne_zero
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hd
  exact cyclic_source_ratio (complexEmbedding φ) (by have := N.range; omega)
    N.omega N.primitive (sourceNormalize U) (source_normalized_member φ F hτ N B hB)

end Source
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedCyclic
end
