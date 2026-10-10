import Holant.Certificates.TetrahedralAffine.AncestorWitnesses
import Holant.Certificates.TetrahedralAffine.Semantics
import Holant.Certificates.TetrahedralAffine.Binaries

/-! Full Lemma9.16 in the unchanged computational basis: all three source
ancestors and all twelve actual tetrahedral binaries have actual affine witnesses. -/
namespace Holant.Certificates.TetrahedralAffine
open Holant Holant.Tractable Holant.Certificates.MatchingProductBridge
noncomputable section

def PreservingOrientation (τ : Fin 3 → Fin 4) : Prop :=
  τ = ![0,1,3] ∨ τ = ![1,3,0] ∨ τ = ![3,0,1]

theorem preserving_iff (τ : Fin 3 → Fin 4) :
    PreservingOrientation τ ↔ ∃ s : Orientation, τ = sigma s := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨s,rfl⟩
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- The source's original complex-valued f_sigma has this exact algebraic lift;
its affine certificate never changes coordinates or rescales its entries. -/
theorem source_ancestor_affine (s : Orientation) :
    ∃ f : Signature AlgebraicComplex 6, Affine f ∧
      ∀ x, (f x : ℂ) = complexAncestor s x :=
  ⟨ancestor s,ancestor_affine s,coe_ancestor s⟩

theorem every_preserving_orientation (τ : Fin 3 → Fin 4) (h : PreservingOrientation τ) :
    ∃ s : Orientation, τ = sigma s ∧
      ∃ f : Signature AlgebraicComplex 6, Affine f ∧ ∀ x, (f x : ℂ) = complexAncestor s x := by
  obtain ⟨s,hs⟩ := (preserving_iff τ).mp h
  exact ⟨s,hs,source_ancestor_affine s⟩

theorem source_binary_affine (r : Representative) :
    ∃ f : Signature AlgebraicComplex 2, Affine f ∧
      ∀ x, (f x : ℂ) = complexBinary r (x 0) (x 1) :=
  ⟨binary r,binary_affine r,coe_binary r⟩

/-- Every literal tetrahedral representative is covered, not just a selected
subfamily of available binaries. The actual binary in this convention is KX. -/
theorem every_tetrahedral_binary_affine {K : Binary} (hK : tetrahedralBase K) :
    ∃ f : Signature AlgebraicComplex 2, Affine f ∧
      ∀ x, (f x : ℂ) = multiply K X (x 0) (x 1) := by
  obtain ⟨r,rfl⟩ := base_covered hK
  exact source_binary_affine r

/-- Full current Lemma9.16. Both tensor families use the same literal Boolean
coordinates and the existing source-level affine class. -/
theorem orientation_preserving_tensors_affine :
    (∀ s : Orientation, Affine (ancestor s) ∧
      ∀ x, (ancestor s x : ℂ) = complexAncestor s x) ∧
    (∀ r : Representative, Affine (binary r) ∧
      ∀ x, (binary r x : ℂ) = complexBinary r (x 0) (x 1)) ∧
    Fintype.card Representative = 12 :=
  ⟨fun s => ⟨ancestor_affine s,coe_ancestor s⟩,
    fun r => ⟨binary_affine r,coe_binary r⟩,representative_card⟩

end
end Holant.Certificates.TetrahedralAffine
