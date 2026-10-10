import Holant.Marked.Monomial

/-!
Source-parameter interface for Lemma 6.26, the marked-sector dictionary.
The projective groups are independent literal families; actual binary transport
and contraction always retain their fixed nonzero representative multipliers.

These are identities for fixed actual ordered binary tables with the stated
sector-coordinate BX transfer. Physical realizability of those representatives
is input provenance: no representative is constructed merely from group
membership, and no analytic coordinate matrix U is asserted to be a gadget.
The completion interface comprises `marked_sector_dictionary`,
`actual_unique_lift`, `chain_unique_lift`, and the reversal theorems in
`Holant.Marked.Reversal`. Unique lifts refer to the transformed bilinear
expansion; the original physical-coordinate expansion need not be monomial.
-/
namespace Holant.Marked
open Tractable
noncomputable section

/-- Precisely the three source sectors and their permitted parameter ranges.
The chosen algebraic square root is input data, as in the manuscript. -/
inductive Parameters (m : ℕ) where
  | M (range : 3 ≤ m)
  | B (range : 3 ≤ m)
  | A (range : 4 ≤ m) (even : Even m) (eta s : Scalar)
      (eta_root : Roots (2 * m) eta) (eta_not_root : ¬ Roots m eta)
      (square : s ^ 2 = eta⁻¹)

namespace Parameters
variable {m : ℕ}

theorem positive (P : Parameters m) : 0 < m := by
  cases P <;> omega

theorem square_root_ne_zero {eta s : Scalar} (heta : eta ≠ 0)
    (hsq : s ^ 2 = eta⁻¹) : s ≠ 0 := by
  intro hs
  have hh : eta⁻¹ ≠ 0 := inv_ne_zero heta
  apply hh
  simpa [hs] using hsq.symm

def basis : Parameters m → InvertibleKernel
  | .M _ => InvertibleKernel.identity
  | .B _ => basisB
  | .A hm _ eta s he _ hsq =>
      basisA s (square_root_ne_zero (he.ne_zero (by omega)) hsq)

def group : Parameters m → Set Mat
  | .M _ => groupM m
  | .B _ => groupB m
  | .A _ _ eta _ _ _ _ => groupA m eta

def edgeNormal : Parameters m → Mat
  | .M _ => Signature.disequality
  | .B _ => Signature.equality
  | .A _ _ eta _ _ _ _ => diagonalKernel 1 (-eta⁻¹)

def edgeMultiplier : Parameters m → Scalar
  | .M _ => 1
  | .B _ => -2 * imaginaryUnit
  | .A _ _ _ _ _ _ _ => 2

theorem edgeMultiplier_ne_zero (P : Parameters m) : P.edgeMultiplier ≠ 0 := by
  cases P with
  | M => exact one_ne_zero
  | B => exact edgeB_multiplier_ne_zero
  | A => change (2 : Scalar) ≠ 0; norm_num

theorem edge_exact (P : Parameters m) :
    sectorEdge P.basis = scale P.edgeMultiplier P.edgeNormal := by
  cases P with
  | M hm =>
    change Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix = _
    rw [edgeM]
    funext a b; simp [scale, edgeMultiplier, edgeNormal]
  | B hm => exact edgeB
  | A hm he eta s hr hn hs => exact edgeA_eta hs

theorem conjugates_group (P : Parameters m) (T : Mat) :
    T ∈ groupM m ↔ conjugate P.basis T ∈ P.group := by
  cases P with
  | M hm => simp [basis, group, conjugate, InvertibleKernel.identity]
  | B hm => exact groupB_conjugate_iff m T
  | A hm he eta s hr hn hs =>
    exact groupA_conjugate_iff m (square_root_ne_zero (hr.ne_zero (by omega)) hs)
      (hr.ne_zero (by omega)) hs T

/-- Explicit surjectivity, using the certified inverse coordinate change. -/
theorem conjugates_group_onto (P : Parameters m) {V : Mat} (hV : V ∈ P.group) :
    ∃ T ∈ groupM m, conjugate P.basis T = V := by
  refine ⟨conjugate P.basis.symm V, ?_, conjugate_inverse' P.basis V⟩
  apply (P.conjugates_group _).mpr
  simpa only [conjugate_inverse'] using hV

theorem is_group (P : Parameters m) : IsProjectiveMatrixGroup P.group :=
  (groupM_is_group P.positive).of_conjugate P.basis P.conjugates_group

theorem edge_isMonomial (P : Parameters m) : IsMonomial (sectorEdge P.basis) := by
  rw [P.edge_exact]
  apply IsMonomial.scale _ P.edgeMultiplier_ne_zero
  cases P with
  | M => exact disequality_isMonomial
  | B => exact equality_isMonomial
  | A hm he eta s hr hn hs =>
    exact diagonal_isMonomial one_ne_zero (neg_ne_zero.mpr (inv_ne_zero (hr.ne_zero (by omega))))

theorem edgeInverse_isMonomial (P : Parameters m) :
    IsMonomial (sectorEdgeInverse P.basis) := by
  cases P with
  | M hm => rw [basis, edgeInverseM]; exact disequality_isMonomial
  | B hm =>
    rw [basis, edgeInverseB]
    exact equality_isMonomial.scale (div_ne_zero imaginaryUnit_ne_zero (by norm_num))
  | A hm he eta s hr hn hs =>
    simp only [basis]
    rw [edgeInverseA_eta _ hs]
    exact (diagonal_isMonomial one_ne_zero (neg_ne_zero.mpr (hr.ne_zero (by omega)))).scale
      (by norm_num)

/-- Actual representatives become monomial by the proved transfer dictionary,
not by a definition that presupposes their transformed shape. -/
theorem actual_isMonomial (P : Parameters m) (B T : Mat) (hT : T ∈ groupM m)
    (hB : ProjectivelyEqual (sectorTransfer P.basis B) T) :
    IsMonomial (transport P.basis B) :=
  ((groupM_isMonomial P.positive hT).mul P.edgeInverse_isMonomial).projective
    (transport_dictionary P.basis B T hB)

/-- A source-sector physical fusion has exactly one internal lift whenever its
boundary entry is nonzero. Its two physical representative scalars are retained. -/
theorem actual_unique_lift (P : Parameters m) (B D T V : Mat)
    (hT : T ∈ groupM m) (hV : V ∈ groupM m)
    (hB : ProjectivelyEqual (sectorTransfer P.basis B) T)
    (hD : ProjectivelyEqual (sectorTransfer P.basis D) V) (a b : Bool) :
    transport P.basis (fuse Signature.disequality B D) a b ≠ 0 ↔
      ∃! ij : Bool × Bool,
        transport P.basis B a ij.1 * sectorEdge P.basis ij.1 ij.2 *
          transport P.basis D ij.2 b ≠ 0 := by
  rw [transport_fuse]
  exact P.edge_isMonomial.fuse_unique_lift (P.actual_isMonomial B T hT hB)
    (P.actual_isMonomial D V hV hD) a b

/-- The source dictionary, with projective statements witnessed by nonzero
scalars and its bilinear fusion identity retaining the exact edge matrix. -/
theorem marked_sector_dictionary (P : Parameters m) :
    (∀ T, T ∈ groupM m ↔ conjugate P.basis T ∈ P.group) ∧
    sectorEdge P.basis = scale P.edgeMultiplier P.edgeNormal ∧
    P.edgeMultiplier ≠ 0 ∧
    (∀ B T, ProjectivelyEqual (sectorTransfer P.basis B) T →
      ProjectivelyEqual (transport P.basis B) (Kernel.mul T (sectorEdgeInverse P.basis))) ∧
    (∀ T V, Kernel.mul
      (Kernel.mul (Kernel.mul T (sectorEdgeInverse P.basis)) (sectorEdge P.basis))
      (Kernel.mul V (sectorEdgeInverse P.basis)) =
        Kernel.mul (Kernel.mul T V) (sectorEdgeInverse P.basis)) ∧
    (∀ B, transport P.basis (Kernel.transpose B) = Kernel.transpose (transport P.basis B)) :=
  ⟨P.conjugates_group, P.edge_exact, P.edgeMultiplier_ne_zero,
    transport_dictionary P.basis, normal_form_fusion P.basis, transport_reversal P.basis⟩

end Parameters
end
end Holant.Marked
