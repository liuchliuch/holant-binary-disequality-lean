import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.A0DenseCanonical
import Holant.Proofs.Dichotomy.Main.PaperControlled.A0SingularResolved

/-! Dense actual A0 q4 is completely consumed. Both the canonical gauge and
the genuine singular escape terminate in one compatible original-current
basis or a real original-G counting-hardness source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.A0DenseResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

include N core literal stable in
theorem fullParity_classified (p : Bool)
    (full : ∀x,GlobalCloseCompletionA0Quaternary.normalized G q x≠0 ↔ parity x=p) :
    GlobalCloseCompletionA0EqualityOriginal.CurrentTract G P ∨
      PaperControlledHardness.Original G := by
  cases PaperControlled.A0DenseCanonical.fullParity_or_bad G P torsion N q core literal p full with
  | inl witness =>
      exact PaperControlled.A0DenseCanonical.canonical_classified G P torsion N q core literal
        (Classical.choice witness).canonical
  | inr bad =>
      have singular := GlobalCloseCompletionA0DenseEscape.bad_original_singular G P torsion N q core literal stable bad
      exact PaperControlled.A0SingularResolved.classified G P torsion N q core literal
        (Classical.choice singular) p full

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.A0DenseResolved
end
