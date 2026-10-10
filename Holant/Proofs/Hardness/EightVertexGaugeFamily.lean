import Holant.Proofs.Hardness.EightVertexGaugeMixedPhysical
import Holant.Proofs.Hardness.EightVertexGaugeFlipPairOutcome
import Holant.Proofs.Hardness.EightVertexGaugeParity

/-! Simultaneous gauge-family closure. The source F can contain other labels,
but the positive conclusion is exactly for the displayed gauge rows and I.
One selected original port weight supplies the SINGLE basis for all rows and
native X. Failed original/flipped decks or mixed-anchor tests give an actual
nonzero binary outside the same complete monomial group. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFamily
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open EightVertexGaugePhysicalOutcome EightVertexGaugeAffine EightVertexGaugeRepresentativeLines
open EightVertexGaugeParity

def rows {ι : Type} (a : ι → AlgebraicComplex) (u : ι → Fin 4 → AlgebraicComplex) :
    SignatureFamily AlgebraicComplex :=
  {f | f = ⟨2,kernelSignature Signature.equality⟩ ∨ ∃ i, f = ⟨4,weighted (a i) (u i)⟩}

def BadBinary (F : SignatureFamily AlgebraicComplex) (m : ℕ) : Prop :=
  ∃ B : Mat, B ≠ 0 ∧ B ∉ groupM m ∧ Gadget.Realizes F .disequality (kernelSignature B) ∧
    BinaryParity B

private theorem bad_of_line {m : ℕ} (hm : 0 < m) (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F m) (B : Mat) (nonzero : B ≠ 0)
    (outside : ¬ ActualMonomialLine reps B)
    (actual : Gadget.Realizes F .disequality (kernelSignature B))
    (parity : BinaryParity B) : BadBinary F m :=
  ⟨B,nonzero,fun hg => outside ((line_iff_group hm F reps B).mpr hg),actual,parity⟩

/-- The basis anchor is fixed BEFORE quantifying over all family members.
All tests and all failures use the same original source F and native X. -/
theorem common_basis_or_physical_escape {ι : Type} {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m)
    (a : ι → AlgebraicComplex) (u : ι → Fin 4 → AlgebraicComplex) (base : ι)
    (ha : ∀ i, a i ≠ 0) (hu : ∀ i j, u i j ≠ 0)
    (actual : ∀ i, Gadget.Realizes F .disequality (weighted (a i) (u i))) :
    IsCommonKBasis affineClass (rows a u) (diagonalBasis (u base 0) (hu base 0)) ∨
      BadBinary F m := by
  classical
  by_cases originals : ∀ i, ∀ k : Fin 3, MonomialPhysicalDeck reps (row (a i) (u i) k)
  · have same (i : ι) : ∀ j, u i j ^ 4 = u i 0 ^ 4 :=
      physical_decks_fourths hm F reps (a i) (u i) (ha i) (hu i) (originals i)
    let v := EightVertexGaugeFlipPairAlgebra.weights (u base)
    let c := a base*u base 2*u base 3
    have hv : ∀ j, v j ≠ 0 := EightVertexGaugeFlipPairAlgebra.weights_nonzero (u base) (hu base)
    have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (ha base) (hu base 2)) (hu base 3)
    have actualFlip : Gadget.Realizes F .disequality (weighted c v) := by
      rw [← EightVertexGaugeFlipPairAlgebra.value (a base) (u base) (hu base)]
      exact EightVertexGaugeFlipPairOutcome.flip_actual F hI _ (actual base)
    by_cases flipped : ∀ k : Fin 3, MonomialPhysicalDeck reps (row c v k)
    · have sameFlip := physical_decks_fourths hm F reps c v hc hv flipped
      have eighth := EightVertexGaugeFlipPairAlgebra.eighth_power (u base) (hu base 0)
        (same base) sameFlip
      by_cases anchors : ∀ i, u i 0 ^ 4 = u base 0 ^ 4
      · left
        refine ⟨(common_affine_basis (u base 0) (hu base 0)).1,?_⟩
        rintro f (rfl | ⟨i,rfl⟩)
        · exact identity_affine_of_eighth (u base 0) (hu base 0) eighth
        · change Affine ((diagonalBasis (u base 0) (hu base 0)).symm.action
            (weighted (a i) (u i)))
          rw [diagonal_action]
          apply weighted_affine
          intro j
          rw [div_pow,same i j,anchors i]
          exact div_self (pow_ne_zero 4 (hu base 0))
      · push Not at anchors
        obtain ⟨i,different⟩ := anchors
        obtain ⟨e,f,cross,order,p,t,hn,ho,hr⟩ := EightVertexGaugeMixedPhysical.physical_escape
          hm F hI reps (a i) (a base) (u i) (u base) (ha i) (ha base) (hu i) (hu base)
          (same i) (same base) different (actual i) (actual base)
        exact Or.inr ⟨_,hn,ho,hr,physical_card_parity F reps _
          (onPorts_even _ _ _ _ e f cross) order p t⟩
    · obtain ⟨i,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps c v actualFlip flipped
      exact Or.inr (bad_of_line (by omega) F reps _ hn ho hr
        (physical_card_parity F reps _ (onPorts_even _ _ _ _ _ _ _) e p t))
  · push Not at originals
    obtain ⟨i,k,missing⟩ := originals
    obtain ⟨j,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps (a i) (u i) (actual i)
      (fun h => missing (h k))
    exact Or.inr (bad_of_line (by omega) F reps _ hn ho hr
      (physical_card_parity F reps _ (onPorts_even _ _ _ _ _ _ _) e p t))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFamily
end
