import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0EqualityOriginal
import Holant.Proofs.Dichotomy.Main.PaperControlled.A0SparseEq4
import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal

/-! The genuine generic literal-X negative theorem consumes the actual A0
Eq4/pins/X whole-current source. Thus a sparse current A0 prime q4 has no
unresolved ordinary-CSP obstruction: the original current family is tractable,
or the original G oracle is counting-hard. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.A0LiteralXTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionA0CurrentSource (mapped SparseOutput)
end C
namespace S
export GlobalCloseCompletionBEqualityCSP (field presentation arity table eq4Label pinLabel xLabel
  eq4_literal pin_literal x_literal)
end S
namespace O
export GlobalCloseCompletionA0EqualityOriginal (ordinarySource family CurrentTract classified)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (d : GlobalCloseCompletionBPrimeEq4.Output (C.mapped G P torsion q core literal))

def source : GenericLiteralXSource.Data G where
  K := S.field (C.mapped G P torsion q core literal) d
  degree := _
  F := S.presentation (C.mapped G P torsion q core literal) d
  size := _
  b := S.arity (C.mapped G P torsion q core literal) d
  H := S.table (C.mapped G P torsion q core literal) d
  e := S.eq4Label (C.mapped G P torsion q core literal)
  p := S.pinLabel (C.mapped G P torsion q core literal)
  x := S.xLabel (C.mapped G P torsion q core literal)
  he := S.eq4_literal (C.mapped G P torsion q core literal) d
  hp := S.pin_literal (C.mapped G P torsion q core literal) d
  hx := S.x_literal (C.mapped G P torsion q core literal) d
  toOriginal := O.ordinarySource G P torsion N q core literal d

@[simp] theorem family_exact : GenericLiteralXSource.family G (source G P torsion N q core literal d)=
    O.family G P torsion q core literal d := rfl

include N in
theorem countingHard
    (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (O.family G P torsion q core literal d))) :
    PaperControlledHardness.Original G :=
  PaperControlledOrdinary.literalX_countingHard G (source G P torsion N q core literal d) negative

include N d in
theorem classified : O.CurrentTract G P ∨ PaperControlledHardness.Original G := by
  rcases O.classified G P torsion q core literal d with tract|negative
  · exact Or.inl tract
  · exact Or.inr (countingHard G P torsion N q core literal d negative)

include N d in
theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ PaperControlledHardness.Original G := by
  rcases classified G P torsion N q core literal d with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G P tract)
  · exact Or.inr hard

variable (stable : ∀f∈rawDeck P.family torsion q,
  Holant.Certificates.MatchingContractionClosure.MatchingOrZero
    (Holant.Projective.BoundedTorsion.actualTransfers P.family) f)
variable (sparse : C.SparseOutput G P torsion q core literal)

include N stable sparse in
theorem sparse_classified : O.CurrentTract G P ∨ PaperControlledHardness.Original G := by
  have result := PaperControlled.A0SparseEq4.eq4_or_hard G P torsion N q core literal stable sparse
  cases result with
  | inl witness => exact classified G P torsion N q core literal (Classical.choice witness)
  | inr hard => exact Or.inr hard

include N core literal stable in
theorem dense_or_classified :
    (∃p,GlobalCloseCompletionA0CurrentSource.FullParity G q p) ∨ O.CurrentTract G P ∨ PaperControlledHardness.Original G := by
  cases GlobalCloseCompletionA0CurrentSource.sparse_or_full G P torsion N q core literal stable with
  | inl dense => exact Or.inl dense
  | inr witness => exact Or.inr (sparse_classified G P torsion N q core literal stable (Classical.choice witness))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.A0LiteralXTerminal
end
