import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinaryTerminal
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentEvenCSPSource

/-! The finite ordinary-family criterion is attached to the exact physical
whole-family two-pin source and squared-CSP source, both terminating at original
G. No new source family, basis, or computational backend is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinarySourceTerminal
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace T
export StableHigherCurrentOrdinaryTerminal
  (family Test Obstruction whole_family_terminal family_preprocessed family_finite)
end T
namespace S
export StableHigherCurrentEvenCSPSource (current ordinary ordinaryArity squareToOriginal)
end S
namespace O
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source (palette_ambient)
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev currentFamily := UniversalPairReduction.FiniteFamily.family (S.current G P)
variable (A : QuaternaryEqualityTerminal.AnchorStep (currentFamily G P))

theorem current_finite : (currentFamily G P).Finite := Set.finite_range _

theorem current_preprocessed : Preprocessed (currentFamily G P) := by
  rintro f ⟨i,rfl⟩
  refine ⟨P.positive i,?_⟩
  intro hz
  apply P.nonzero i
  funext x
  apply (StableHigherCurrentPurePinsCore.embedding G).injective
  exact (congrFun hz x).trans (map_zero _).symm

/-- This is the table actually evaluated by the joint arbitrary-occurrence
source, embedded coefficientwise into algebraic complex numbers. -/
def physicalFamily : SignatureFamily AlgebraicComplex :=
  Set.range fun i : Fin (P.count+3) =>
    RingHomRealization.mapAny (O.K (S.current G P) A).subtype
      (⟨S.ordinaryArity G P A i.val,S.ordinary G P A i⟩ :
        AnySignature (O.K (S.current G P) A))

/-- Every current row and both literal pins are exactly the finite test's
rows; its common matrix is the physical source's original anchor matrix. -/
theorem physical_family_exact : physicalFamily G P A=T.family A :=
  O.palette_ambient (S.current G P) A

theorem physical_family_preprocessed : Preprocessed (physicalFamily G P A) := by
  rw [physical_family_exact]
  exact T.family_preprocessed A (current_preprocessed G P)

theorem physical_family_finite : (physicalFamily G P A).Finite := Set.finite_range _

def Classified : Prop :=
  (T.Test (physicalFamily G P A) ∧
    (CommonKPresentationInKCoordinates affineClass (currentFamily G P) ∨
      CommonKPresentationInKCoordinates productClass (currentFamily G P) ∨
      CommonKPresentationInKCoordinates localAffineClass (currentFamily G P))) ∨
  T.Obstruction (physicalFamily G P A)

theorem classified : Classified G P A := by
  unfold Classified
  rw [physical_family_exact]
  exact T.whole_family_terminal A (current_finite G P) (current_preprocessed G P)

/-- Both source programmes are concrete constructed outputs. The negative
alternative retains its finite obstructions and does not claim hardness. -/
structure Receipt : Type 1 where
  ordinarySource : {programme // programme=StableHigherCurrentAnchorPins.toOriginal G P A}
  squaredSource : {programme // programme=S.squareToOriginal G P A}
  result : Classified G P A

def produce : Receipt G P A :=
  ⟨⟨StableHigherCurrentAnchorPins.toOriginal G P A,rfl⟩,
    ⟨S.squareToOriginal G P A,rfl⟩,classified G P A⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinarySourceTerminal
end
