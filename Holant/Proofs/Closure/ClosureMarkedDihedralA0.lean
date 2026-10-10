import Holant.Proofs.Closure.ClosureMarkedDihedralCoordinates
import Holant.Proofs.Closure.ClosureMarkedReversalRouting

/-! Constructed UNSHIFTED native-X dihedral branch A^0. This is a distinct
manuscript branch and is not forced into Parameters.A's shifted eta guard.
Its fixed Hadamard basis already lies in the original field, keeps the edge
exactly 2 diag(1,-1), and literal retained equality is never re-anchored.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralA0
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers

abbrev basis := ClosureMarkedCyclic.basis
abbrev normalize := ClosureMarkedCyclic.normalize
abbrev normalized := ClosureMarkedCyclic.normalized

theorem nativeZ_to_X : normalize zClass = xClass := by
  change (pglMk ℂ ClosureMarkedCyclic.ambientCoordinates)⁻¹ * pglMk ℂ zGL *
    pglMk ℂ ClosureMarkedCyclic.ambientCoordinates = pglMk ℂ xGL
  rw [← map_inv,← map_mul,← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨1,one_ne_zero,?_⟩
  have hi : ((ClosureMarkedCyclic.ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Matrix Bool Bool ℂ) =
      Matrix.map (Matrix.of basis.inverse) ClosureMarkedDihedral.inclusion := rfl
  change (ClosureMarkedCyclic.ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ).val * zGL.val *
    ClosureMarkedCyclic.ambientCoordinates.val = _
  rw [hi]
  ext a b
  cases a <;> cases b <;>
    norm_num [ClosureMarkedCyclic.ambientCoordinates,ClosureMarkedCyclic.coordinateGL,
      basis,ClosureMarkedCyclic.basis,basisA,UA,UAInv,Matrix.mul_apply,Fintype.sum_bool,
      xGL,antidiagonalGL,antidiagonal,zGL,diagonalGL,diagonal,ClosureMarkedDihedral.inclusion] <;>
    first
    | change (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1; norm_num
    | change (2 : ℂ)⁻¹ - (2 : ℂ)⁻¹ = 0; ring
    | change -(2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 0; ring

theorem normalized_centralizer (H : Subgroup (PGL2 ℂ))
    (hH : H ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ))) :
    normalized H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
  rintro q ⟨r,hr,rfl⟩
  have hc : Commute r xClass := Subgroup.mem_centralizer_singleton_iff.mp (hH hr)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := (hc.map normalize.toMonoidHom).eq
  change normalize r * normalize xClass = normalize xClass * normalize r at h
  rwa [ClosureMarkedCyclic.nativeX_to_Z] at h

structure NativeA0 (H : Subgroup (PGL2 ℂ)) where
  selected : ClosureMarkedDihedral.NativeM (normalized H)
  even : Even selected.m
  range : 4 ≤ selected.m

def nativeA0 (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : H ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (hx : xClass ∈ H) (hz : zClass ∈ H) (h2 : Nat.card H ≠ 2) (h4 : Nat.card H ≠ 4) : NativeA0 H := by
  let e := H.equivMapOfInjective normalize.toMonoidHom normalize.injective
  letI : Finite (normalized H) := Finite.of_equiv H e.toEquiv
  have hc : Nat.card (normalized H) = Nat.card H := Nat.card_congr e.toEquiv.symm
  have hx' : xClass ∈ normalized H := ⟨zClass,hz,nativeZ_to_X⟩
  let N := ClosureMarkedDihedral.nativeM (normalized H) (normalized_centralizer H hH) hx'
    (hc ▸ h2) (hc ▸ h4)
  have hp : pauliSubgroup ≤ H := by
    change Subgroup.closure ({xClass,zClass} : Set (PGL2 ℂ)) ≤ H
    rw [Subgroup.closure_le]
    rintro q (rfl | hq)
    · exact hx
    · exact Set.mem_singleton_iff.mp hq ▸ hz
  have hd := Subgroup.card_dvd_of_le hp
  rw [pauli_card,← hc,N.cardinal] at hd
  have hev : Even N.m := by
    rcases hd with ⟨k,hk⟩
    exact ⟨k,by omega⟩
  have hr : 4 ≤ N.m := by
    have hh := N.range
    obtain ⟨k,hk⟩ := hev
    omega
  exact ⟨N,hev,hr⟩

namespace NativeA0
variable {H : Subgroup (PGL2 ℂ)} (N : NativeA0 H)

theorem same_edge : sectorEdge basis = scale 2 (diagonalKernel 1 (-1)) := ClosureMarkedCyclic.same_edge

theorem same_reversal (B : Holant.Marked.Mat) :
    transport basis (Kernel.transpose B) = Kernel.transpose (transport basis B) := transport_reversal _ B

end NativeA0
namespace Source
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]

def nativeA0 (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hX : group φ F hτ ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (hZ : zClass ∈ group φ F hτ)
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    NativeA0 (group φ F hτ) := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  exact ClosureMarkedDihedralA0.nativeA0 _ hX (nativeX_mem φ F hτ hI) hZ h2 h4

theorem actual_sector_spectrum (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : NativeA0 (group φ F hτ)) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    sectorTransfer basis (Matrix.map B φ) ∈ groupM N.selected.m :=
  ClosureMarkedDihedralCoordinates.Source.actual_sector_spectrum basis φ F hτ N.selected B hB

/-- Full inverse ordered binary-row coverage, using the derived even order.
The transformed edge scalar two and the original source key are explicit. -/
theorem standard_source_representative (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (N : NativeA0 (group φ F hτ))
    (p : Bool) (t : Scalar) (ht : Roots N.selected.m t) :
    ∃ j : completeGroup F hτ, ∃ c : Scalar, c ≠ 0 ∧
      transport basis (Matrix.map (actualRepresentative F hτ j) φ) =
        scale c (ClosureMarkedDihedral.standard p t) := by
  have ht' : Roots N.selected.m (-t) := by
    unfold Roots at *
    rw [neg_pow,N.even.neg_one_pow,one_mul,ht]
  obtain ⟨j,c,hc,he⟩ := ClosureMarkedDihedralCoordinates.Source.source_sector_representative
    basis φ F hτ N.selected p (-t) ht'
  refine ⟨j,c/2,div_ne_zero hc (by norm_num),?_⟩
  rw [transport_eq_transfer,he]
  have hi : sectorEdgeInverse basis = scale (1/2) (diagonalKernel 1 (-1)) := by
    simpa [basis,ClosureMarkedCyclic.basis] using
      (edgeInverseA_eta (s:=1) (eta:=1) one_ne_zero (by simp : (1:Scalar)^2 = 1⁻¹))
  rw [hi,scale_mul]
  have hs : Kernel.mul (ClosureMarkedDihedral.standard p (-t)) (diagonalKernel 1 (-1)) =
      ClosureMarkedDihedral.standard p t := by
    funext a b
    cases p <;> cases a <;> cases b <;>
      simp [ClosureMarkedDihedral.standard,R,S,diagonalKernel,Kernel.mul_apply,Signature.disequality]
  rw [hs]
  simp [div_eq_mul_inv]

end Source
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralA0
end
