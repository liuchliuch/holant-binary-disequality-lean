import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeChartAnchor
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorPins

/-! The compatible dense native-M row installs the actual equality anchor's
whole-current-family ordinary two-pin programme. The incompatible alternative
keeps the existing singular receipt over the same original palette. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeAnchorContinuation
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.FinitePGL2.Stabilization
open StableDenseGaugeCurrent
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

/-- The programme is fixed by this exact actual anchor. All transformed
current labels, Eq4, and both unaries share its one ordinary coordinate table. -/
structure AnchorReceipt : Type 1 where
  anchor : QuaternaryEqualityTerminal.AnchorStep (ClosureSourceRows.ambientFamily G P)
  installed : { programme // programme =
    StableHigherCurrentAnchorPins.fromAmbientToOriginal G P anchor }

def install (A : QuaternaryEqualityTerminal.AnchorStep (ClosureSourceRows.ambientFamily G P)) :
    AnchorReceipt G P :=
  ⟨A,⟨StableHigherCurrentAnchorPins.fromAmbientToOriginal G P A,rfl⟩⟩

inductive Outcome : Type 1 where
  | anchor (receipt : AnchorReceipt G P)
  | singular (receipt : SingularReceipt G P)

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

/-- The guard theorem uses only the old palette's complete native-M group.
The resulting ordinary source is constructed after that mathematical exit. -/
def fromRow (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
    (products : StableDenseResidualAlgebra.Products q) : Outcome G P :=
  Classical.choice (by
    rcases StableDenseGaugeEqualityAnchor.row_anchorStep_or_original_singular
      G P torsion N q actual even dense products with anchor | singular
    · obtain ⟨A⟩ := anchor
      exact ⟨Outcome.anchor (install G P A)⟩
    · obtain ⟨r⟩ := singular
      exact ⟨Outcome.singular r⟩)

/-- The actual stable dense-parity core supplies the chart and its products
internally, including an originally odd parity support. The terminal programme
still uses the whole original current palette and its original-G oracle. -/
def fromCurrent (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
    (literal : core.signature = ⟨4,q⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion q,
      Holant.Certificates.MatchingContractionClosure.MatchingOrZero
        (Holant.Projective.BoundedTorsion.actualTransfers P.family) g)
    (p : Bool) (full : ∀ x, q x ≠ 0 ↔ parity x = p) : Outcome G P :=
  Classical.choice (by
    rcases StableDenseGaugeChartAnchor.current_anchorStep_or_original_singular
      G P torsion N q core literal stable p full with anchor | singular
    · obtain ⟨A⟩ := anchor
      exact ⟨Outcome.anchor (install G P A)⟩
    · obtain ⟨r⟩ := singular
      exact ⟨Outcome.singular r⟩)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeAnchorContinuation
end
