import Holant.Proofs.Tetrahedral.EvenCSPReduction.Program
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinarySquareProgramme
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorPins

/-! A real arbitrary-even-occurrence CSP caller and its squared-row input
compiler, followed by the exact whole-current-family anchor/pin programme.
Both ends keep their actual finite field and validated byte codecs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentEvenCSPSource
open Holant Holant.Algebraic Holant.Complexity Holant.Tractable Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

section Generic
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (H : (i : Fin s) → Signature K (a i.val))
variable (j4 : Fin s) (literal : (⟨a j4.val,H j4⟩ : AnySignature K)=
  ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

def tables := QuaternaryOrdinaryCompanion.tables F H

theorem query_value (r : Raw.Input s a) :
    (tables F H).evaluate F (Compilation.query r H j4 literal)=Raw.value H r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  exact Compilation.query_denote r H j4 literal

def controlled : LengthControlledOracleReduction (Raw.validatedEncoding s a) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (Raw.value H) ((tables F H).evaluate F) :=
  controlledOneQueryOfEq (Program.computes H j4 literal) (identityComputes F.encoding)
    ((tables F H).outputBound F) (Raw.value H) (fun r => (query_value F H j4 literal r).symm)

def squareControlled : LengthControlledOracleReduction
    (StableHigherCurrentOrdinarySquareProgramme.inputEncoding s a) F.encoding
    (Raw.validatedEncoding s a) F.encoding
    (fun r => StableHigherCurrentOrdinarySquare.value (StableHigherCurrentOrdinarySquare.square H) r.val)
    (Raw.value H) :=
  controlledOneQueryOfEq (StableHigherCurrentOrdinarySquareProgramme.queryComputes s a)
    (identityComputes F.encoding) (controlled F H j4 literal).sourceOutputBound
    (fun r => StableHigherCurrentOrdinarySquare.value (StableHigherCurrentOrdinarySquare.square H) r.val)
    (fun r => (StableHigherCurrentOrdinarySquareProgramme.query_value H r).symm)

def squareGraphControlled := Programme.compose (squareControlled F H j4 literal)
  (controlled F H j4 literal)
end Generic

section Current
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace O
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (palette paletteArity palette_original)
end O
namespace One
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (F K)
end One
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (A : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (StableHigherCurrentPurePinsCore.mapped G P)))

abbrev current := StableHigherCurrentPurePinsCore.mapped G P
abbrev ordinary := O.palette (current G P) A
abbrev ordinaryArity := O.paletteArity (current G P) A
abbrev field := One.F (current G P) A
local instance : Algebra ℚ (One.K (current G P) A) := (One.K (current G P) A).algebra'

def eq4Label : Fin (P.count+3) := ⟨P.count,by omega⟩
theorem eq4_literal :
    (⟨ordinaryArity G P A (eq4Label G P).val,ordinary G P A (eq4Label G P)⟩ :
      AnySignature (One.K (current G P) A))=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ :=
  (O.palette_original (current G P) A (QuaternaryOrdinaryCompanion.eq4Index (s:=P.count))).trans
    (QuaternaryOrdinaryCompanion.decoded_eq4 (current G P) A)

/-- Unrestricted CSP on the actual entire squared ordinary pin family has
its internally generated even-degree query and final original-G programme. -/
def squareToOriginal := PhysicalProgramme.ofControlled (Programme.compose
  (squareGraphControlled (field G P A) (ordinary G P A) (eq4Label G P) (eq4_literal G P A))
  (StableHigherCurrentAnchorPins.toOriginal G P A).controlled)
end Current

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentEvenCSPSource
end
