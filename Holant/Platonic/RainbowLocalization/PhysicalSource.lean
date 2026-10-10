import Holant.Platonic.RainbowLocalization.PhysicalRealization

/-! Physical rainbow localization with canonical source cards and actual
kernel representatives.  The exact native macro and the nonzero scalar of
its actual realization over the retained family are recorded separately.
No encoded Turing-reduction statement is asserted here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure MatchingCut
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}
variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}

/-- Every physical output is a genuine six-port signature.  Its exact
relation to the one-ancestor macro retains the substitution multiplier. -/
structure PhysicalLocalization (A : ActualKernelLift Λ D) (G : Set (Binary (K := ℂ)))
    (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n) (K₀ K₁ K₂ : Kernel ℂ)
    (D₀ D₁ D₂ : Presentation ℂ P) where
  algebraic : AlgebraicLocalization D₀ D₁ D₂
  kernels : Fin algebraic.common.edges → D
  realization_scalar : ℂ
  realization_scalar_ne_zero : realization_scalar ≠ 0
  surviving_scale_ne_zero : realization_scalar * localizationScale A algebraic kernels ≠ 0
  signature : Signature ℂ 6
  signature_eq : signature = realization_scalar • localizationSignature A algebraic p kernels f
  realized : Gadget.Realizes Λ .disequality signature
  nonzero : signature ≠ 0
  card₀ : cardMap (sixPortOrder algebraic) signature K₀ =
    (realization_scalar * localizationScale A algebraic kernels) • algebraic.exceptional₀.tensor
  card₁ : cardMap (sixPortOrder algebraic) signature K₁ =
    (realization_scalar * localizationScale A algebraic kernels) • algebraic.exceptional₁.tensor
  card₂ : cardMap (sixPortOrder algebraic) signature K₂ =
    (realization_scalar * localizationScale A algebraic kernels) • algebraic.exceptional₂.tensor
  kernel_safe : ∀ e, SafeBinary G (A.binary (kernels e))
  all_cards : ∀ u v : Fin 6, u ≠ v → ∀ K ∈ D,
    contractPair u v K signature = 0 ∨ ∃ M : Presentation ℂ (Remaining u v),
      M.edges = 2 ∧ M.scalar ≠ 0 ∧ (∀ e, (M.matrix e).det ≠ 0 ∧ SafeBinary G (M.matrix e)) ∧
      contractPair u v K signature = M.tensor

variable {A : ActualKernelLift Λ D} {G : Set (Binary (K := ℂ))}
variable {p : Bool ⊕ P ≃ Fin n} {f : Signature ℂ n} {K₀ K₁ K₂ : Kernel ℂ}
variable {D₀ D₁ D₂ : Presentation ℂ P}

def PhysicalLocalization.graph (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) : Network ℂ 6 :=
  localizationNetwork A T.algebraic p T.kernels f

theorem PhysicalLocalization.graph_value (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) :
    T.signature = T.realization_scalar • T.graph.denote := T.signature_eq

theorem PhysicalLocalization.kernel_count (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) :
    Fintype.card (Fin T.algebraic.common.edges) = (n - 6) / 2 := by
  rw [Fintype.card_fin,original_kernel_count T.algebraic p]

theorem PhysicalLocalization.original_vertex_count (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) :
    (Finset.univ.filter (fun v : Option (Fin T.algebraic.common.edges) =>
      (nativeCollectionFinite (originalClosurePorts T.algebraic p) (effectiveKernels A T.kernels) f).arity v = n)).card = 1 :=
  localization_original_vertex_count A T.algebraic p T.kernels f

theorem PhysicalLocalization.binary_vertex_count (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) :
    (Finset.univ.filter (fun v : Option (Fin T.algebraic.common.edges) =>
      (nativeCollectionFinite (originalClosurePorts T.algebraic p) (effectiveKernels A T.kernels) f).arity v = 2)).card = (n - 6) / 2 :=
  localization_binary_vertex_count A T.algebraic p T.kernels f

theorem PhysicalLocalization.vertex_labels (T : PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) :
    (nativeCollectionFinite (originalClosurePorts T.algebraic p) (effectiveKernels A T.kernels) f).vertex none = f ∧
    ∀ e, (nativeCollectionFinite (originalClosurePorts T.algebraic p) (effectiveKernels A T.kernels) f).vertex (some e) =
      binarySignature (A.binary (T.kernels e)) :=
  actualCollection_vertex_labels A T.kernels (originalClosurePorts T.algebraic p) f

/-- Source physical clause from the concrete contents of a deck-stable
marked state: actual complete kernel representatives, canonical safe cards,
and three nonsingular rainbow images of an actual rich domain line. -/
theorem source_physical_localization
    (A : ActualKernelLift Λ D) (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (hf : Gadget.Realizes Λ .disequality f)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    (hD : D ⊆ G) (hcomplete : CompleteKernelRepresentatives G D)
    (hspan : Submodule.span ℂ D = ⊤)
    (hdeck : ∀ u v : Fin n, u < v → ∀ K ∈ D, MatchingOrZero G (contractPair u v K f))
    (K₀ K₁ K₂ : Kernel ℂ) (hK₀ : K₀ ∈ D) (hK₁ : K₁ ∈ D) (hK₂ : K₂ ∈ D)
    (hline : K₂ ∈ Submodule.span ℂ ({K₀,K₁} : Set (Kernel ℂ)))
    (hcard₀ : cardMap p f K₀ = D₀.tensor) (hcard₁ : cardMap p f K₁ = D₁.tensor)
    (hcard₂ : cardMap p f K₂ = D₂.tensor)
    (h₀ : ∀ e, (D₀.matrix e).det ≠ 0) (h₁ : ∀ e, (D₁.matrix e).det ≠ 0)
    (h₂ : ∀ e, (D₂.matrix e).det ≠ 0)
    (hc₀ : D₀.scalar ≠ 0) (hc₁ : D₁.scalar ≠ 0) (hc₂ : D₂.scalar ≠ 0)
    (hne₀₁ : (presentationMatching D₀).mate ≠ (presentationMatching D₁).mate)
    (hne₂₀ : (presentationMatching D₂).mate ≠ (presentationMatching D₀).mate)
    (hne₂₁ : (presentationMatching D₂).mate ≠ (presentationMatching D₁).mate) :
    Nonempty (PhysicalLocalization A G p f K₀ K₁ K₂ D₀ D₁ D₂) := by
  have hsafe := actualKernel_safe G hG hX D hD
  have hordered := all_orderings_of_canonical G hG hX hrev D hD hcomplete f hdeck
  obtain ⟨L,C,hc,hout,he₀,he₁,he₂,hvertices,hedges,hall⟩ :=
    source_physical_graph_localization A p f G hG hX hrev hsafe hspan hordered
      K₀ K₁ K₂ hK₀ hK₁ hK₂ hline hcard₀ hcard₁ hcard₂
      h₀ h₁ h₂ hc₀ hc₁ hc₂ hne₀₁ hne₂₀ hne₂₁
  obtain ⟨c,hcn,hreal⟩ := localization_actual_representative A L p C f hf
  refine ⟨{
    algebraic := L
    kernels := C
    realization_scalar := c
    realization_scalar_ne_zero := hcn
    surviving_scale_ne_zero := mul_ne_zero hcn hc
    signature := c • localizationSignature A L p C f
    signature_eq := rfl
    realized := hreal
    nonzero := smul_ne_zero hcn hout
    card₀ := ?_
    card₁ := ?_
    card₂ := ?_
    kernel_safe := localization_actual_kernels_safe A L C G hG hX hsafe
    all_cards := ?_
  }⟩
  · rw [cardMap_smul_tensor,he₀,smul_smul]
  · rw [cardMap_smul_tensor,he₁,smul_smul]
  · rw [cardMap_smul_tensor,he₂,smul_smul]
  · intro u v huv K hK
    apply quaternary_of_safe_card G hG _ u v huv K
    rw [contractPair_tensor_smul]
    exact matchingOrZero_smul G _ (hall u v huv K hK) c

end Holant.Platonic.RainbowLocalization.Physical
