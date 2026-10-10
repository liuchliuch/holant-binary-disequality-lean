import Holant.EightVertex.ProductAnchor.Classification
import Holant.EightVertex.ProductAnchor.NativeNetworks
import Holant.OpenNetworkComposition.ProjectiveContraction
import Holant.OpenNetworkComposition.DisjointTensor
import Holant.Dihedral.CompatibleClosure.ActualReindex

/-! Manuscript Lemma 4.2, all structural and physical clauses. The transformed
native edge is included in the common product witness. The equality anchor is
realized over every original resource family already realizing q, including
realizations with free stubs and disconnected scalar components. -/
namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Substitute arbitrary actual realizations into the literal template. The
only exceptional closure multiplier is the proved nonzero wire-circle factor. -/
theorem realizes_anchorTemplate (F : SignatureFamily Scalar) (q : Signature Scalar 4)
    (hq : Gadget.Realizes F .disequality q) (s : Word4) :
    Gadget.RealizesUpTo F .disequality (anchorTemplate Signature.disequality s q) := by
  unfold anchorTemplate
  split
  · refine ⟨1,one_ne_zero,?_⟩
    simpa using hq
  · have ht := OpenNetworkComposition.realizes_tensor F .disequality q q hq hq
    have hp := Dihedral.CompatibleClosure.realizes_reindex F .disequality
      (Signature.tensor q q) ht (wiringEquiv s)
    have hfirst := OpenNetworkComposition.realizes_contract F _ hp (by norm_num)
    exact OpenNetworkComposition.realizesUpTo_contract F _ hfirst (by norm_num)

/-- Full physical dense-case assertion, stronger than the retained finite-family
specialization: every family realizing the original q realizes an equality anchor. -/
theorem dense_realizing_family_anchor (q : Signature Scalar 4) (h : DenseForm q)
    (F : SignatureFamily Scalar) (hq : Gadget.Realizes F .disequality q) : HasEqualityAnchor F := by
  obtain ⟨R,s,c,hc,hR,hT⟩ := dense_native_template_normalized q h
  exact equality_anchor_of_template F q R s c hc hR hT (realizes_anchorTemplate F q hq s)

/-- The source's third outcome includes both its entry formula and the actual
realization consequence; neither is replaced by a caller-supplied hypothesis. -/
def DenseAnchorOutcome (q : Signature Scalar 4) : Prop :=
  DenseForm q ∧ ∀ F : SignatureFamily Scalar,
    Gadget.Realizes F .disequality q → HasEqualityAnchor F

/-- Lemma 4.2: exactly one source outcome, with every nonzero scalar and original
port partition retained. Common transformability is the singleton convention in
K coordinates and uses one actual algebraic matrix for q and its native X edge. -/
theorem source_product_transformable_eight_vertex (q : Signature Scalar 4)
    (he : EndpointEven q)
    (hP : CommonKPresentationInKCoordinates productClass {⟨4,q⟩}) :
    (PureEquality q ∧ ¬TwoWeightedEqualities q ∧ ¬DenseAnchorOutcome q) ∨
    (TwoWeightedEqualities q ∧ ¬PureEquality q ∧ ¬DenseAnchorOutcome q) ∨
    (DenseAnchorOutcome q ∧ ¬PureEquality q ∧ ¬TwoWeightedEqualities q) := by
  have hx := structural_alternatives_exclusive q
  rcases common_product_structural_classification q he hP with h | h | h
  · exact Or.inl ⟨h,fun h' => hx.1 ⟨h,h'⟩,fun h' => hx.2.1 ⟨h,h'.1⟩⟩
  · exact Or.inr (Or.inl ⟨h,fun h' => hx.1 ⟨h',h⟩,fun h' => hx.2.2 ⟨h,h'.1⟩⟩)
  · exact Or.inr (Or.inr ⟨⟨h,dense_realizing_family_anchor q h⟩,
      fun h' => hx.2.1 ⟨h',h⟩,fun h' => hx.2.2 ⟨h',h⟩⟩)

/-- Explicit full even support in outcome 3. -/
theorem dense_anchor_support {q : Signature Scalar 4} (h : DenseAnchorOutcome q) (x : Word4) :
    q x≠0 ↔ Holant.weight x%2=0 := h.1.nonzero_iff_even x

end
end Holant.EightVertex.ProductAnchor
