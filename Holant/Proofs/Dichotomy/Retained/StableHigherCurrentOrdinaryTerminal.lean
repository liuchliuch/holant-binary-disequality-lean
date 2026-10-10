import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorLocalCriterion
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorProductFamily
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorCommonBasis

/-! Whole-family ordinary classification with finite shared-basis tests. Eq4
eliminates four exceptional clauses and makes Product literal. Both pins and
Eq4 reduce Affine to at most 6480 fixed matrices; both pins reduce LocalAffine
to sixteen fixed bases. Rejection retains explicit edge or row witnesses and
does not assert a hardness theorem for the unresolved negative CSP branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinaryTerminal
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.LocalDrafts.MainChain
namespace A
export StableHigherCurrentAnchorAffineBasisCandidates
  (inverseCandidates common_transformable_iff_candidates inverseCandidates_card_le)
end A
namespace L
export StableHigherCurrentAnchorLocalCriterion (candidateBasis common_transformable_iff_candidates)
export StableHigherCurrentAnchorLocalBasis (pin)
end L
namespace P
export StableHigherCurrentAnchorProductFamily (common_product_iff_literal)
end P
open StableHigherCurrentAnchorCriterion (eq4 eq4_nonzero tract_iff_one_common_basis)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def AffineTest (H : SignatureFamily AlgebraicComplex) : Prop :=
  ∃N∈A.inverseCandidates,∃hN : determinant N≠0,
    IsCommonBasis affineClass H (invertibleOfDeterminant N hN).symm

def LocalTest (H : SignatureFamily AlgebraicComplex) : Prop :=
  ∃opposite : Bool,∃q : Fin 8,IsCommonBasis localAffineClass H (L.candidateBasis opposite q)

def Test (H : SignatureFamily AlgebraicComplex) : Prop :=
  AffineTest H ∨ H ⊆ productClass ∨ LocalTest H

theorem pin_nonzero (b : Bool) : L.pin b≠0 := by
  intro h
  have h' := congrFun h (fun _=>b)
  simpa [L.pin] using h'

theorem pin_preprocess {H : SignatureFamily AlgebraicComplex} {b : Bool}
    (h : (⟨1,L.pin b⟩ : AnySignature AlgebraicComplex)∈H) :
    (⟨1,L.pin b⟩ : AnySignature AlgebraicComplex)∈preprocess H :=
  ⟨h,by norm_num,pin_nonzero b⟩

/-- A literal finite criterion for all retained rows, with a single candidate
chosen before checking every row and the mandatory ordinary equality edge. -/
theorem tract_iff_finite_test {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,L.pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,L.pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (heq : (⟨4,eq4⟩ : AnySignature AlgebraicComplex)∈H) :
    Tract H ↔ (preprocess H).Finite ∧ Test (preprocess H) := by
  have hp : (⟨4,eq4⟩ : AnySignature AlgebraicComplex)∈preprocess H :=
    ⟨heq,by decide,eq4_nonzero⟩
  rw [tract_iff_one_common_basis heq,
    A.common_transformable_iff_candidates (pin_preprocess h0) (pin_preprocess h1) hp,
    P.common_product_iff_literal hp,
    L.common_transformable_iff_candidates (pin_preprocess h0) (pin_preprocess h1)]
  change (_ ∧ AffineTest _) ∨ (_ ∧ _) ∨ (_ ∧ LocalTest _) ↔ _ ∧ Test _
  unfold Test
  tauto

/-- Concrete reason a fixed common-basis candidate fails. Either its actual
edge fails, or an actual retained row fails in that same basis. -/
def Rejected (C H : SignatureFamily AlgebraicComplex) (B : InvertibleKernel) : Prop :=
  (⟨2,kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
    AnySignature AlgebraicComplex)∉C ∨
  ∃f∈H,(⟨f.1,B.symm.action f.2⟩ : AnySignature AlgebraicComplex)∉C

theorem rejected_iff (C H : SignatureFamily AlgebraicComplex) (B : InvertibleKernel) :
    Rejected C H B ↔ ¬IsCommonBasis C H B := by
  classical
  simp only [Rejected,IsCommonBasis,not_and_or,not_forall,exists_prop]

def Obstruction (H : SignatureFamily AlgebraicComplex) : Prop :=
  (∀N∈A.inverseCandidates,∀hN : determinant N≠0,
    Rejected affineClass H (invertibleOfDeterminant N hN).symm) ∧
  (∃f∈H,f∉productClass) ∧
  (∀opposite : Bool,∀q : Fin 8,Rejected localAffineClass H (L.candidateBasis opposite q))

theorem obstruction_iff (H : SignatureFamily AlgebraicComplex) :
    Obstruction H ↔ ¬Test H := by
  classical
  simp only [Obstruction,rejected_iff,Test,AffineTest,LocalTest,not_or,not_exists,
    not_and,Set.subset_def,not_forall,exists_prop]

/-- Failure has explicit witnesses against every admissible finite candidate,
plus a literal non-Product row. No singleton classification is substituted. -/
theorem not_tract_iff_obstruction {H : SignatureFamily AlgebraicComplex}
    (finite : (preprocess H).Finite)
    (h0 : (⟨1,L.pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,L.pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (heq : (⟨4,eq4⟩ : AnySignature AlgebraicComplex)∈H) :
    ¬Tract H ↔ Obstruction (preprocess H) := by
  rw [tract_iff_finite_test h0 h1 heq,obstruction_iff]
  simp only [finite,true_and]

/-- The actual semantic ordinary family produced by the anchor and two-pin
caller: every current row under the same matrix, Eq4, and both literal pins. -/
def family {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) : SignatureFamily AlgebraicComplex :=
  ((familyAction B.basis F ∪ {⟨4,eq4⟩}) ∪ {⟨1,L.pin false⟩}) ∪ {⟨1,L.pin true⟩}

theorem family_eq4 {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) :
    (⟨4,eq4⟩ : AnySignature AlgebraicComplex)∈family B :=
  Or.inl (Or.inl (Or.inr rfl))

theorem family_false {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) :
    (⟨1,L.pin false⟩ : AnySignature AlgebraicComplex)∈family B :=
  Or.inl (Or.inr rfl)

theorem family_true {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) :
    (⟨1,L.pin true⟩ : AnySignature AlgebraicComplex)∈family B := Or.inr rfl

theorem family_finite {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) (finite : F.Finite) : (family B).Finite :=
  (((finite.image _).union (Set.finite_singleton _)).union
    (Set.finite_singleton _)).union (Set.finite_singleton _)

theorem family_preprocessed {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) (preprocessed : Preprocessed F) :
    Preprocessed (family B) := by
  intro f hf
  rcases hf with ((hf|rfl)|rfl)|rfl
  · exact Conformal.preprocessed_familyAction B.basis preprocessed f hf
  · exact ⟨by decide,eq4_nonzero⟩
  · exact ⟨by decide,pin_nonzero false⟩
  · exact ⟨by decide,pin_nonzero true⟩

/-- Accepted candidates classify the entire original current family in one
native basis, retaining the original disequality edge and its exact scale. -/
theorem native_of_test {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) (finite : F.Finite)
    (preprocessed : Preprocessed F) (test : Test (family B)) :
    CommonKPresentationInKCoordinates affineClass F ∨
    CommonKPresentationInKCoordinates productClass F ∨
    CommonKPresentationInKCoordinates localAffineClass F := by
  apply StableHigherCurrentAnchorCommonBasis.native_common_of_ordinary_tract
    B preprocessed (fun _ h=>Or.inl (Or.inl (Or.inl h))) (family_eq4 B)
  apply (tract_iff_finite_test (family_false B) (family_true B) (family_eq4 B)).mpr
  rw [preprocess_eq_self (family_preprocessed B preprocessed)]
  exact ⟨family_finite B finite,test⟩

/-- Exhaustive mathematical terminal: either an explicit finite shared-basis
test succeeds and pulls back to the whole native family, or all candidates
have retained concrete obstructions. The latter still needs a hardness proof. -/
theorem whole_family_terminal {F : SignatureFamily AlgebraicComplex}
    (B : QuaternaryEqualityTerminal.AnchorStep F) (finite : F.Finite)
    (preprocessed : Preprocessed F) :
    (Test (family B) ∧ (CommonKPresentationInKCoordinates affineClass F ∨
      CommonKPresentationInKCoordinates productClass F ∨
      CommonKPresentationInKCoordinates localAffineClass F)) ∨ Obstruction (family B) := by
  classical
  by_cases test : Test (family B)
  · exact Or.inl ⟨test,native_of_test B finite preprocessed test⟩
  · exact Or.inr ((obstruction_iff _).mpr test)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinaryTerminal
end
