import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralInducedMap
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralProducts

/-! Coefficient extraction from the preserved marked-octahedral proof. Actual left/right O actions on the eighteen four-root
lines. Only old root indices and the old proved multiplication table occur.
The four marked rows use the same indices; their analytic chart is not a
physical resource. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open scoped Matrix

def baseLine : Fin 122 := 28

/-- Computed indices in the original 24-entry palette, not conjugators. -/
def orbitPair (t : Fin 122) : Fin 24 × Fin 24 :=
  match t.val with
  | 28 => (0,0) | 41 => (11,4) | 54 => (10,5)
  | 63 => (0,4) | 64 => (5,0) | 73 => (6,0)
  | 74 => (2,4) | 75 => (4,5) | 82 => (4,0)
  | 83 => (3,5) | 92 => (0,5) | 93 => (7,0)
  | 96 => (6,4) | 103 => (8,5) | 104 => (9,4)
  | 115 => (7,4) | 116 => (11,5) | 121 => (2,0)
  | _ => (0,0)

def movedIndex (a b r : Fin 24) : Fin 24 :=
  Products.productIndex a (Products.productIndex r b)

def movedScale (a b r : Fin 24) : Scalar :=
  Products.productScale r b * Products.productScale a (Products.productIndex r b)

def movedLine (a b : Fin 24) : Finset (Fin 24) :=
  (globalLine .octahedral baseLine).image (movedIndex a b)

/-- Exact eighteen-line orbit certificate. The other 104 old secants are
not silently removed: the implication applies exactly to old fourLines. -/
theorem finite_line_orbit : ∀ t : Fin 122,t ∈ fourLines →
    movedLine (orbitPair t).1 (orbitPair t).2 = globalLine .octahedral t := by
  change ∀t : Fin 122,t∈fourLines →
    movedLine (orbitPair t).1 (orbitPair t).2=octahedralSecants t
  intro t ht
  have literals : fourLines = {28,41,54,63,64,73,74,75,82,83,92,93,96,103,104,115,116,121} := by decide +kernel
  rw [literals] at ht
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem baseLine_mem : baseLine ∈ fourLines := by decide +kernel

theorem base_pair : canonicalPair baseLine = ![0,1] := by decide +kernel

theorem movedScale_ne (a b r : Fin 24) : movedScale a b r ≠ 0 :=
  mul_ne_zero (Products.productScale_nonzero r b)
    (Products.productScale_nonzero a (Products.productIndex r b))

noncomputable section

theorem kernel_product (f : Form) (a b : Fin 24) :
    kernel f a * kernel f b = embed (Products.productScale a b) •
      kernel f (Products.productIndex a b) := by
  unfold kernel
  rw [← complexMatrix_mm,← theta_mm,Products.standard_product,theta_ms,complexMatrix_ms]

/-- The finite permutation above is the action of the actual typed kernels,
with the exact nonzero old product scalar restored. -/
theorem moved_point (f : Form) (a b r : Fin 24) :
    sandwich (kernel f a) (kernel f b) *ᵥ point f r =
      embed (movedScale a b r) • point f (movedIndex a b r) := by
  rw [sandwich_action]
  change coordinates (kernel f a * assemble (quaternionCoefficient (kernel f r)) * kernel f b) = _
  rw [assemble_coefficient,Matrix.mul_assoc,kernel_product,Matrix.mul_smul,kernel_product]
  rw [smul_smul,map_smul,← embed_mul]
  rfl

theorem moved_scalar_ne (a b r : Fin 24) : embed (movedScale a b r) ≠ 0 :=
  fun h => movedScale_ne a b r (embed_injective (h.trans embed_zero.symm))

/-- Both directions keep the ORIGINAL root index, its nonzero scalar and
its same-row kernel action. No caller supplies a full group or a plane. -/
theorem actual_line_orbit (f : Form) (t : Fin 122) (ht : t ∈ fourLines) :
    (∀ r ∈ globalLine .octahedral baseLine,
      movedIndex (orbitPair t).1 (orbitPair t).2 r ∈ globalLine .octahedral t) ∧
    (∀ s ∈ globalLine .octahedral t,∃ r ∈ globalLine .octahedral baseLine,
      s = movedIndex (orbitPair t).1 (orbitPair t).2 r ∧
      sandwich (kernel f (orbitPair t).1) (kernel f (orbitPair t).2) *ᵥ point f r =
        embed (movedScale (orbitPair t).1 (orbitPair t).2 r) • point f s ∧
      embed (movedScale (orbitPair t).1 (orbitPair t).2 r) ≠ 0) := by
  have he := finite_line_orbit t ht
  constructor
  · intro r hr
    rw [← he]
    exact Finset.mem_image.mpr ⟨r,hr,rfl⟩
  · intro s hs
    rw [← he] at hs
    obtain ⟨r,hr,hrs⟩ := Finset.mem_image.mp hs
    exact ⟨r,hr,hrs.symm,hrs ▸ moved_point f _ _ r,moved_scalar_ne _ _ r⟩

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
