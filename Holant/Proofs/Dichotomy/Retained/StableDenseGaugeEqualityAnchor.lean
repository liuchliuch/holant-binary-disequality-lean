import Holant.Proofs.Hardness.EightVertexGaugeEqualityAnchor
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeCurrent
import Holant.Proofs.Algorithms.QuaternaryEqualityTerminal

/-! The dense gauge branch produces an actual equality anchor over the
original current palette, or the existing original-field singular receipt.
No subsequently supplied computational pin is tested against the old complete
group. Anchor coordinates retain their algebraic field and actual graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeEqualityAnchor
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open StableDenseGaugeCurrent

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
include torsion N

/-- The primitive root and all physical representatives come from precisely
the old palette's complete native-M group. -/
theorem ambient_anchor_or_original_singular (M : Signature AlgebraicComplex 4)
    (actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality M)
    (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
    (products : StableDenseResidualAlgebra.Products M) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor (ClosureSourceRows.ambientFamily G P) ∨
      Nonempty (SingularReceipt G P) := by
  rcases EightVertexGaugeEqualityAnchor.dense_anchor_or_bad N.range N.omega N.primitive
    (ClosureSourceRows.ambientFamily G P) (ambient_identity G P)
    (representatives G P torsion N) M actual even dense products with anchor | bad
  · exact Or.inl anchor
  · obtain ⟨B,hn,ho,hr,hp⟩ := bad
    exact Or.inr (singular_receipt G P torsion N B hn ho hr hp)

/-- The coefficient map is used only to transport the original input row;
the equality anchor's coordinate matrix is not asserted to descend. -/
theorem row_anchor_or_original_singular (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
    (products : StableDenseResidualAlgebra.Products q) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor (ClosureSourceRows.ambientFamily G P) ∨
      Nonempty (SingularReceipt G P) := by
  let M := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
  have hactual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality M :=
    RingHomRealization.realizes_map (ClosureSourceRows.embedding G) actual
  have heven : EvenSupport M := by
    intro x hx
    change ClosureSourceRows.embedding G (q x) = 0
    rw [even x hx,map_zero]
  have hdense : StableDenseParityAlgebra.Dense M := by
    simpa [M,StableDenseParityAlgebra.Dense,entries,RingHomRealization.mapSignature] using dense
  have hproducts : StableDenseResidualAlgebra.Products M := by
    refine ⟨?_,?_,?_⟩
    · simpa [M,entries,RingHomRealization.mapSignature] using
        congrArg (ClosureSourceRows.embedding G) products.1
    · simpa [M,entries,RingHomRealization.mapSignature] using
        congrArg (ClosureSourceRows.embedding G) products.2.1
    · simpa [M,entries,RingHomRealization.mapSignature] using
        congrArg (ClosureSourceRows.embedding G) products.2.2
  exact ambient_anchor_or_original_singular G P torsion N M hactual heven hdense hproducts

/-- An actual executable anchor receipt, with its graph, matrix and both
nonzero normalizing scalars retained for the whole-family continuation. -/
theorem row_anchorStep_or_original_singular (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
    (products : StableDenseResidualAlgebra.Products q) :
    Nonempty (QuaternaryEqualityTerminal.AnchorStep (ClosureSourceRows.ambientFamily G P)) ∨
      Nonempty (SingularReceipt G P) := by
  rcases row_anchor_or_original_singular G P torsion N q actual even dense products with
    anchor | singular
  · exact Or.inl (QuaternaryEqualityTerminal.anchorStep_exists anchor)
  · exact Or.inr singular

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeEqualityAnchor
end
