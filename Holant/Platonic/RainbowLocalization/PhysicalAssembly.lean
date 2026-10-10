import Holant.Platonic.RainbowLocalization.PhysicalPorts
import Holant.Platonic.RainbowLocalization.PhysicalKernelLift

/-! The localized six-port graph, its three preserved marked cards, and
its complete inherited safe-card condition.  Every actual lift scalar is kept. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure MatchingCut
open scoped BigOperators
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}
variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {D₀ D₁ D₂ : Presentation ℂ P}

def localizationNetwork (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n) : Network ℂ 6 :=
  actualCollectionNetwork A C (originalClosurePorts L p) f

def localizationSignature (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n) : Signature ℂ 6 :=
  (localizationNetwork A L p C f).denote

def localizationScale (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (C : Fin L.common.edges → D) : ℂ := realizationScale A C * closureScale L (fun e => (C e).val)

theorem localizationScale_ne_zero (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (C : Fin L.common.edges → D) (hC : ∀ e, Kernel.pair (C e).val (L.common.matrix e) ≠ 0) :
    localizationScale A L C ≠ 0 := by
  apply mul_ne_zero (realizationScale_ne_zero A C)
  exact mul_ne_zero L.common_scalar (Finset.prod_ne_zero_iff.mpr (fun e _ => hC e))

theorem localized_card (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n)
    (K : Kernel ℂ) (F : Tensor ℂ P) (q : Tensor ℂ (Side (cut L.ports) true))
    (hcard : cardMap p f K = F)
    (hF : ∀ x, F x = q (fun p => x p.val) * L.common.tensor (fun p => x p.val)) :
    cardMap (sixPortOrder L) (localizationSignature A L p C f) K = localizationScale A L C • q := by
  rw [localizationSignature,localizationNetwork,actualCollection_denote,cardMap_smul_tensor]
  rw [originalClosurePorts,cardMap_full_closure,hcard,close_factorized L _ F q hF,smul_smul]
  rfl

theorem localization_vertices (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n) :
    (localizationNetwork A L p C f).shape.vertices = (n - 6) / 2 + 1 := by
  rw [localizationNetwork,actualCollection_vertices,Fintype.card_fin,original_kernel_count L p]

theorem localization_edges (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n) :
    (localizationNetwork A L p C f).shape.edges = 2 * ((n - 6) / 2) := by
  rw [localizationNetwork,actualCollection_edges,Fintype.card_fin,original_kernel_count L p]

theorem localization_all_cards (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    (hD : ∀ K ∈ D, SafeBinary G K)
    (hdeck : ∀ u v : Fin n, u ≠ v → ∀ K ∈ D, MatchingOrZero G (contractPair u v K f)) :
    ∀ u v : Fin 6, u ≠ v → ∀ K ∈ D,
      MatchingOrZero G (contractPair u v K (localizationSignature A L p C f)) := by
  unfold localizationSignature localizationNetwork actualCollectionNetwork
  rw [nativeCollection_denote]
  exact all_cards_after_collection G hG hX hrev D (originalClosurePorts L p)
    (effectiveKernels A C) f (effectiveKernels_safe A C G hG hD) hdeck

theorem remaining_six_card (u v : Fin 6) (huv : u ≠ v) : Fintype.card (Remaining u v) = 4 := by
  let e : Remaining u v ≃ (({u,v} : Finset (Fin 6))ᶜ : Finset (Fin 6)) :=
    Equiv.subtypeEquivRight (fun x => by simp [Remaining,not_or])
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_compl]
  simp [huv]

/-- Every surviving actual card is zero or an actual safe quaternary
matching presentation with exactly two binary factors. -/
theorem localization_all_cards_quaternary (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    (hD : ∀ K ∈ D, SafeBinary G K)
    (hdeck : ∀ u v : Fin n, u ≠ v → ∀ K ∈ D, MatchingOrZero G (contractPair u v K f)) :
    ∀ u v : Fin 6, u ≠ v → ∀ K ∈ D,
      contractPair u v K (localizationSignature A L p C f) = 0 ∨
      ∃ M : Presentation ℂ (Remaining u v), M.edges = 2 ∧ M.scalar ≠ 0 ∧
        (∀ e, (M.matrix e).det ≠ 0 ∧ SafeBinary G (M.matrix e)) ∧
        contractPair u v K (localizationSignature A L p C f) = M.tensor := by
  intro u v huv K hK
  rcases localization_all_cards A L p C f G hG hX hrev hD hdeck u v huv K hK with
    hz | ⟨M,hM,hc,he⟩
  · exact Or.inl hz
  · have hcM := (presentationMatching M).port_card
    rw [remaining_six_card u v huv] at hcM
    have hm : M.edges = 2 := by change 4 = 2 * M.edges at hcM; omega
    exact Or.inr ⟨M,hm,hc,fun e => ⟨SafeBinary.nonsingular hG (hM e),hM e⟩,he⟩

/-- Actual kernels are selected from the spanning set and applied to the
original f vertex.  Their three chosen rich-line cards survive with the same
explicit nonzero scalar, and every other actual output card stays safe. -/
theorem source_physical_graph_localization
    (A : ActualKernelLift Λ D) (p : Bool ⊕ P ≃ Fin n) (f : Signature ℂ n)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    (hD : ∀ K ∈ D, SafeBinary G K) (hspan : Submodule.span ℂ D = ⊤)
    (hdeck : ∀ u v : Fin n, u ≠ v → ∀ K ∈ D, MatchingOrZero G (contractPair u v K f))
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
    ∃ (L : AlgebraicLocalization D₀ D₁ D₂) (C : Fin L.common.edges → D),
      localizationScale A L C ≠ 0 ∧
      localizationSignature A L p C f ≠ 0 ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) K₀ =
        localizationScale A L C • L.exceptional₀.tensor ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) K₁ =
        localizationScale A L C • L.exceptional₁.tensor ∧
      cardMap (sixPortOrder L) (localizationSignature A L p C f) K₂ =
        localizationScale A L C • L.exceptional₂.tensor ∧
      (localizationNetwork A L p C f).shape.vertices = (n - 6) / 2 + 1 ∧
      (localizationNetwork A L p C f).shape.edges = 2 * ((n - 6) / 2) ∧
      ∀ u v : Fin 6, u ≠ v → ∀ K ∈ D,
        MatchingOrZero G (contractPair u v K (localizationSignature A L p C f)) := by
  have himage := card_line_from_domain p f K₀ K₁ K₂ hline
  rw [hcard₀,hcard₁,hcard₂] at himage
  obtain ⟨L⟩ := algebraic_localization D₀ D₁ D₂ h₀ h₁ h₂ hc₀ hc₁ hc₂
    hne₀₁ hne₂₀ hne₂₁ himage
  have hn (e : Fin L.common.edges) : L.common.matrix e ≠ 0 := by
    intro he
    exact L.common_det e (by rw [he]; simp)
  obtain ⟨C,hC,hp,hprod⟩ := choose_actual_closing_kernels D hspan L.common.matrix hn
  let C' : Fin L.common.edges → D := fun e => ⟨C e,hC e⟩
  have hs : localizationScale A L C' ≠ 0 := localizationScale_ne_zero A L C' hp
  have he₀ := localized_card A L p C' f K₀ D₀.tensor L.exceptional₀.tensor hcard₀ L.factor₀
  have he₁ := localized_card A L p C' f K₁ D₁.tensor L.exceptional₁.tensor hcard₁ L.factor₁
  have he₂ := localized_card A L p C' f K₂ D₂.tensor L.exceptional₂.tensor hcard₂ L.factor₂
  have hout : localizationSignature A L p C' f ≠ 0 := by
    intro hz
    have hE := productValue_nonzero L.exceptional₀.ports L.exceptional₀.matrix L.exceptional₀.scalar
      L.exceptional₀_det L.exceptional₀_scalar
    have hh := he₀
    rw [hz,cardMap_zero_tensor] at hh
    exact smul_ne_zero hs hE hh.symm
  exact ⟨L,C',hs,hout,he₀,he₁,he₂,localization_vertices A L p C' f,
    localization_edges A L p C' f,localization_all_cards A L p C' f G hG hX hrev hD hdeck⟩

end Holant.Platonic.RainbowLocalization.Physical
