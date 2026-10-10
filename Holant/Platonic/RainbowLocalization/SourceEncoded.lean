import Holant.Platonic.RainbowLocalization.EncodedReduction
import Holant.Platonic.RainbowLocalization.PhysicalCanonicalDeck
import Holant.Platonic.RainbowLocalization.PhysicalOccurrence
import Holant.NetworkAsGadget

/-! The complete physical and encoded-reduction clauses of source Lemma9.9.
The separate algebraic source theorem supplies uniqueness and exactly three
matching-product points. Here the actual retained family is finite algebraic,
and its ordinary one-ancestor macro supplies the actual polynomial reduction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure MatchingCut
variable {P : Type*} [Fintype P] [DecidableEq P] {n s : ℕ}
variable {arity : ℕ → ℕ} {D : Set (Kernel ℂ)}
variable {D₀ D₁ D₂ : Presentation ℂ P}

/-- The source's finite retained-family formulation. No supplied graph labelling,
field coordinates, machine compiler correctness or reduction premise occurs. -/
theorem source_rainbow_localization_encoded
    (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x))
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D)
    (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (hf : (⟨n,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    (hD : D ⊆ G) (hcomplete : CompleteKernelRepresentatives G D)
    (hspan : Submodule.span ℂ D = ⊤)
    (hdeck : ∀u v : Fin n,u<v → ∀K ∈ D,MatchingOrZero G (contractPair u v K f))
    (K₀ K₁ K₂ : Kernel ℂ) (hK₀ : K₀ ∈ D) (hK₁ : K₁ ∈ D) (hK₂ : K₂ ∈ D)
    (hline : K₂ ∈ Submodule.span ℂ ({K₀,K₁} : Set (Kernel ℂ)))
    (hcard₀ : cardMap p f K₀=D₀.tensor) (hcard₁ : cardMap p f K₁=D₁.tensor)
    (hcard₂ : cardMap p f K₂=D₂.tensor)
    (h₀ : ∀e,(D₀.matrix e).det≠0) (h₁ : ∀e,(D₁.matrix e).det≠0)
    (h₂ : ∀e,(D₂.matrix e).det≠0)
    (hc₀ : D₀.scalar≠0) (hc₁ : D₁.scalar≠0) (hc₂ : D₂.scalar≠0)
    (hne₀₁ : (presentationMatching D₀).mate≠(presentationMatching D₁).mate)
    (hne₂₀ : (presentationMatching D₂).mate≠(presentationMatching D₀).mate)
    (hne₂₁ : (presentationMatching D₂).mate≠(presentationMatching D₁).mate) :
    ∃ (L : AlgebraicLocalization D₀ D₁ D₂) (C : Fin L.common.edges → D),
      localizationScale A L C≠0 ∧ localizationSignature A L p C f≠0 ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) K₀=
        localizationScale A L C • L.exceptional₀.tensor ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) K₁=
        localizationScale A L C • L.exceptional₁.tensor ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) K₂=
        localizationScale A L C • L.exceptional₂.tensor ∧
      (localizationNetwork A L p C f).shape.vertices=(n-6)/2+1 ∧
      (localizationNetwork A L p C f).shape.edges=2*((n-6)/2) ∧
      Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality
        (localizationSignature A L p C f) ∧
      EncodedNativeAdjoin signatures halg (localizationSignature A L p C f) ∧
      ∀u v : Fin 6,u≠v → ∀K ∈ D,
        contractPair u v K (localizationSignature A L p C f)=0 ∨
        ∃M : Presentation ℂ (Remaining u v),M.edges=2 ∧ M.scalar≠0 ∧
          (∀e,(M.matrix e).det≠0 ∧ SafeBinary G (M.matrix e)) ∧
          contractPair u v K (localizationSignature A L p C f)=M.tensor := by
  have hsafe := actualKernel_safe G hG hX D hD
  have hordered := all_orderings_of_canonical G hG hX hrev D hD hcomplete f hdeck
  obtain ⟨L,C,hs,hn,h₀c,h₁c,h₂c,hv,he,hall⟩ :=
    source_physical_graph_localization A p f G hG hX hrev hsafe hspan hordered
      K₀ K₁ K₂ hK₀ hK₁ hK₂ hline hcard₀ hcard₁ hcard₂
      h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₀₁ hne₂₀ hne₂₁
  refine ⟨L,C,hs,hn,h₀c,h₁c,h₂c,hv,he,?_,?_,?_⟩
  · exact Gadget.realizes_network (localizationNetwork A L p C f)
      (indexedRetainedFamily arity signatures) .disequality
      (actualCollection_retained_vertices A C (originalClosurePorts L p) f arity signatures hf hb)
      (fun _ => rfl)
  · exact localization_encoded_adjoin signatures halg A L p C f hf hb
  · exact localization_all_cards_quaternary A L p C f G hG hX hrev hsafe hordered

end Holant.Platonic.RainbowLocalization.Physical
