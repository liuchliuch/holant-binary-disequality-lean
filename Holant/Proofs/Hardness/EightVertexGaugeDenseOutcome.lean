import Holant.Proofs.Hardness.EightVertexGaugePhaseInsertion
import Holant.Proofs.Hardness.EightVertexGaugeRepresentativeLines
import Holant.Proofs.Hardness.EightVertexGaugePhysicalOutcome
import Holant.Proofs.Hardness.EightVertexGaugeFlipPairOutcome
import Holant.Proofs.Hardness.EightVertexGaugeFamily
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeExistence

/-! Original-row endpoint of the gauge continuation. The existing dense
complementary-product equations provide a coefficient factorization, but every
new network retains the original M as its actual vertex label. The conclusion
is an affine singleton common basis or an actual nonzero physical binary
outside the supplied complete monomial representative lines. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeDenseOutcome
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open EightVertexGaugePorts EightVertexGaugePhysicalOutcome

def originalRow (M : Signature AlgebraicComplex 4) (i : Fin 3) : Signature AlgebraicComplex 4 :=
  (EightVertexGaugeTwoRowNetwork.onPorts M M (zeroPair i) (zeroPair i) true).denote

export EightVertexGaugeRepresentativeLines (line_iff_group)

theorem originalRow_even (M : Signature AlgebraicComplex 4)
    (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
    (products : StableDenseResidualAlgebra.Products M) (i : Fin 3) :
    EvenSupport (originalRow M i) := by
  obtain ⟨u,_,hM⟩ := StableDenseResidualGaugeExistence.algebraic_factor M even products
    dense.1 dense.2.1 dense.2.2.1 dense.2.2.2.1 dense.2.2.2.2.1
  unfold originalRow
  rw [hM]
  exact EightVertexGaugeParity.onPorts_even _ _ _ _ _ _ _

theorem selected_even (M : Signature AlgebraicComplex 4)
    (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
    (products : StableDenseResidualAlgebra.Products M) (flip : Bool) (i : Fin 3) :
    EvenSupport (EightVertexGaugeFlipPairOutcome.selected M flip i) := by
  obtain ⟨u,hu,hM⟩ := StableDenseResidualGaugeExistence.algebraic_factor M even products
    dense.1 dense.2.1 dense.2.2.1 dense.2.2.2.1 dense.2.2.2.2.1
  rw [hM]
  cases flip
  · rw [EightVertexGaugeFlipPairOutcome.selected_false]
    exact EightVertexGaugeParity.onPorts_even _ _ _ _ _ _ _
  · rw [EightVertexGaugeFlipPairOutcome.selected_true _ _ hu]
    exact EightVertexGaugeParity.onPorts_even _ _ _ _ _ _ _

/-- No safety condition on a new row is an input. The right branch is a
finite physical obstruction with an actual binary realization over the same
F. Its original vertices, ordered ports, scalars and native edges are retained. -/
theorem dense_basis_or_physical_escape {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (M : Signature AlgebraicComplex 4)
    (actualM : Gadget.Realizes F .disequality M)
    (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
    (products : StableDenseResidualAlgebra.Products M) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass {⟨4,M⟩} B) ∨
      ∃ (i : Fin 3) (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
        physicalCard (originalRow M i) e (reps.matrix p t) ≠ 0 ∧
        physicalCard (originalRow M i) e (reps.matrix p t) ∉ groupM m ∧
        Gadget.Realizes F .disequality
          (kernelSignature (physicalCard (originalRow M i) e (reps.matrix p t))) := by
  obtain ⟨u,hu,hM⟩ := StableDenseResidualGaugeExistence.algebraic_factor M even products
    dense.1 dense.2.1 dense.2.2.1 dense.2.2.2.1 dense.2.2.2.2.1
  have actualWeighted : Gadget.Realizes F .disequality
      (StableDenseResidualGauge.weighted (entries M).a u) := by
    simpa only [← hM] using actualM
  rcases basis_or_physical_escape hm F hI reps (entries M).a u dense.1 hu actualWeighted with
    basis | ⟨i,e,p,t,nonzero,outside,actual⟩
  · exact Or.inl ⟨EightVertexGaugeAffine.diagonalBasis (u 0) (hu 0),
      by simpa only [← hM] using basis⟩
  · have outsideGroup : physicalCard (row (entries M).a u i) e (reps.matrix p t) ∉
        groupM m := fun hg => outside ((line_iff_group (by omega) F reps _).mpr hg)
    exact Or.inr ⟨i,e,p,t,
      by simpa only [row,← hM,originalRow] using nonzero,
      by simpa only [row,← hM,originalRow] using outsideGroup,
      by simpa only [row,← hM,originalRow] using actual⟩

/-- The additional literal two-I test retains one basis for the ORIGINAL M,
the supplied I vertex, and native X. The failing cap is again an actual binary. -/
theorem dense_identity_basis_or_physical_escape {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (M : Signature AlgebraicComplex 4)
    (actualM : Gadget.Realizes F .disequality M)
    (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
    (products : StableDenseResidualAlgebra.Products M) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass
      {⟨4,M⟩,⟨2,kernelSignature Signature.equality⟩} B) ∨
      ∃ (flip : Bool) (i : Fin 3) (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
        physicalCard (EightVertexGaugeFlipPairOutcome.selected M flip i) e (reps.matrix p t) ≠ 0 ∧
        physicalCard (EightVertexGaugeFlipPairOutcome.selected M flip i) e (reps.matrix p t) ∉ groupM m ∧
        Gadget.Realizes F .disequality
          (kernelSignature (physicalCard (EightVertexGaugeFlipPairOutcome.selected M flip i)
            e (reps.matrix p t))) := by
  obtain ⟨u,hu,hM⟩ := StableDenseResidualGaugeExistence.algebraic_factor M even products
    dense.1 dense.2.1 dense.2.2.1 dense.2.2.2.1 dense.2.2.2.2.1
  have actualWeighted : Gadget.Realizes F .disequality
      (StableDenseResidualGauge.weighted (entries M).a u) := by
    simpa only [← hM] using actualM
  rcases EightVertexGaugeFlipPairOutcome.basis_with_identity_or_physical_escape
    hm F hI reps (entries M).a u dense.1 hu actualWeighted with
      basis | ⟨flip,i,e,p,t,nonzero,outside,actual⟩
  · exact Or.inl ⟨EightVertexGaugeAffine.diagonalBasis (u 0) (hu 0),
      by simpa only [← hM] using basis⟩
  · have outsideGroup := fun hg => outside ((line_iff_group (by omega) F reps _).mpr hg)
    exact Or.inr ⟨flip,i,e,p,t,
      by simpa only [← hM] using nonzero,
      by simpa only [← hM] using outsideGroup,
      by simpa only [← hM] using actual⟩

def originalFamily {ι : Type} (M : ι → Signature AlgebraicComplex 4) :
    SignatureFamily AlgebraicComplex :=
  {f | f = ⟨2,kernelSignature Signature.equality⟩ ∨ ∃ i, f = ⟨4,M i⟩}

/-- Every supplied dense residual row shares ONE resulting basis. The
coefficient factorizations are rewritten away from the family statement;
they grant no additional labels to the source gadget family F. -/
theorem dense_family_with_binaries_or_physical_escape {ι : Type} {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (M : ι → Signature AlgebraicComplex 4) (base : ι)
    (actualM : ∀ i, Gadget.Realizes F .disequality (M i))
    (even : ∀ i, EvenSupport (M i)) (dense : ∀ i, StableDenseParityAlgebra.Dense (M i))
    (products : ∀ i, StableDenseResidualAlgebra.Products (M i)) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass
      (originalFamily M ∪ {f | ∃ B : Mat, B∈groupM m ∧ f=⟨2,kernelSignature B⟩}) B) ∨
      EightVertexGaugeFamily.BadBinary F m := by
  have factors (i : ι) : ∃ u : Fin 4 → AlgebraicComplex, (∀ j, u j ≠ 0) ∧
      M i = StableDenseResidualGauge.weighted (entries (M i)).a u :=
    StableDenseResidualGaugeExistence.algebraic_factor (M i) (even i) (products i)
      (dense i).1 (dense i).2.1 (dense i).2.2.1 (dense i).2.2.2.1 (dense i).2.2.2.2.1
  choose u hu equations using factors
  have actualWeighted (i : ι) : Gadget.Realizes F .disequality
      (StableDenseResidualGauge.weighted (entries (M i)).a (u i)) := by
    simpa only [← equations i] using actualM i
  have familyEq : originalFamily M =
      EightVertexGaugeFamily.rows (fun i => (entries (M i)).a) u := by
    ext f
    constructor
    · rintro (h | ⟨i,h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i,h.trans (congrArg
          (fun q : Signature AlgebraicComplex 4 => (⟨4,q⟩ : AnySignature AlgebraicComplex))
          (equations i))⟩
    · rintro (h | ⟨i,h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i,h.trans (congrArg
          (fun q : Signature AlgebraicComplex 4 => (⟨4,q⟩ : AnySignature AlgebraicComplex))
          (equations i).symm)⟩
  rcases EightVertexGaugePhaseInsertion.family_with_binaries_or_bad hm F hI reps
    (fun i => (entries (M i)).a) u base (fun i => (dense i).1) hu actualWeighted with
      basis | bad
  · left
    refine ⟨EightVertexGaugeAffine.diagonalBasis (u base 0) (hu base 0),?_⟩
    rwa [familyEq]
  · exact Or.inr bad

/-- Restrict the stronger common basis without changing its matrix or edge. -/
theorem dense_family_basis_or_physical_escape {ι : Type} {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (M : ι → Signature AlgebraicComplex 4) (base : ι)
    (actualM : ∀ i, Gadget.Realizes F .disequality (M i))
    (even : ∀ i, EvenSupport (M i)) (dense : ∀ i, StableDenseParityAlgebra.Dense (M i))
    (products : ∀ i, StableDenseResidualAlgebra.Products (M i)) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass (originalFamily M) B) ∨
      EightVertexGaugeFamily.BadBinary F m := by
  rcases dense_family_with_binaries_or_physical_escape hm F hI reps M base actualM even dense products
    with ⟨B,basis⟩ | bad
  · exact Or.inl ⟨B,basis.1,fun f hf => basis.2 f (Or.inl hf)⟩
  · exact Or.inr bad

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeDenseOutcome
end
