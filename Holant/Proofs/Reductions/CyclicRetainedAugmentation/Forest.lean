import Holant.Proofs.Reductions.CyclicRetainedAugmentation.Alphabet


noncomputable section
namespace Holant.LocalDrafts.Hardness.CyclicRetainedAugmentation
open Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant.LocalDrafts.FinitePGL2.Stabilization
open GeneralExtraction FactorSaturation

variable {s N : ℕ} {a : ℕ → ℕ} {F : SignatureFamily ℂ}
variable {R : PhysicalAttachments.Representatives F N} {q : Signature ℂ 4}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (d : CountedDoubled R q)
variable (hl : ∀ v, (⟨d.certificate.circuit.network.shape.arity v,
  d.certificate.circuit.network.vertex v⟩ : AnySignature ℂ) ∈
    mapFamily inclusion (CyclicPowerConsumer.family G))
variable (hN : 0 < N) (ha : a s = 2)
variable (hn : ∀ i, G i ≠ 0) (hp : ∀ i : Fin s, 0 < a i.val)
variable (hI : RetainsIdentity (CyclicPowerConsumer.family G))

abbrev D := roots G d hl hN ha hn hp hI
abbrev forest := FactorSaturation.tree (D G d hl hN ha hn hp hI).signature
  (D G d hl hN ha hn hp hI).nonzero
abbrev count := s+1+WholeForest.count (D G d hl hN ha hn hp hI)
abbrev arity := WholeForest.A (D G d hl hN ha hn hp hI)
abbrev catalogue := WholeForest.outputFamily (D G d hl hN ha hn hp hI)
def retained : SignatureFamily AlgebraicComplex :=
  Set.range (fun i => (⟨arity G d hl hN ha hn hp hI i.val,
    catalogue G d hl hN ha hn hp hI i⟩ : AnySignature AlgebraicComplex))

theorem catalogue_root (i : Fin (s+1)) :
    (⟨arity G d hl hN ha hn hp hI i.val,
      catalogue G d hl hN ha hn hp hI ⟨i.val,by omega⟩⟩ : AnySignature AlgebraicComplex) =
        rootSignature G d hl hN ha i :=
  FactorSaturation.lookup_old (D G d hl hN ha hn hp hI).signature
    (D G d hl hN ha hn hp hI).nonzero i

theorem catalogue_old (i : Fin s) :
    (⟨arity G d hl hN ha hn hp hI i.val,
      catalogue G d hl hN ha hn hp hI ⟨i.val,by omega⟩⟩ : AnySignature AlgebraicComplex) =
        ⟨a i.val,G i⟩ :=
  (catalogue_root G d hl hN ha hn hp hI ⟨i.val,by omega⟩).trans (old_label G d hl hN ha i)

theorem catalogue_binary :
    (⟨arity G d hl hN ha hn hp hI s,
      catalogue G d hl hN ha hn hp hI ⟨s,by omega⟩⟩ : AnySignature AlgebraicComplex) =
        ⟨2,CyclicPowerConsumer.factor G d hl hN⟩ :=
  (catalogue_root G d hl hN ha hn hp hI ⟨s,by omega⟩).trans (new_label G d hl hN ha)

theorem retained_exact : retained G d hl hN ha hn hp hI =
    (CyclicPowerConsumer.family G ∪ {⟨2,CyclicPowerConsumer.factor G d hl hN⟩}) ∪
      Set.range (FactorSaturation.entry (D G d hl hN ha hn hp hI).signature
        (D G d hl hN ha hn hp hI).nonzero) := by
  rw [retained,WholeForest.output_labels]
  change Set.range (rootSignature G d hl hN ha) ∪ _ = _
  rw [root_range]

theorem retains_old : CyclicPowerConsumer.family G ⊆ retained G d hl hN ha hn hp hI := by
  rw [retained_exact]
  exact fun _ h => Or.inl (Or.inl h)

theorem retains_binary : (⟨2,CyclicPowerConsumer.factor G d hl hN⟩ : AnySignature AlgebraicComplex) ∈
    retained G d hl hN ha hn hp hI := by
  rw [retained_exact]
  exact Or.inl (Or.inr rfl)

theorem saturated : FactorSaturated (retained G d hl hN ha hn hp hI) :=
  WholeForest.output_saturated (D G d hl hN ha hn hp hI)
theorem finite_retained : (retained G d hl hN ha hn hp hI).Finite :=
  WholeForest.output_finite (D G d hl hN ha hn hp hI)
theorem preprocessed (f : AnySignature AlgebraicComplex)
    (hf : f ∈ retained G d hl hN ha hn hp hI) : 0 < f.1 ∧ f.2 ≠ 0 :=
  WholeForest.output_preprocessed (D G d hl hN ha hn hp hI) f hf
theorem retains_identity : RetainsIdentity (retained G d hl hN ha hn hp hI) :=
  retains_old G d hl hN ha hn hp hI hI

theorem forest_leaves_retained (i : Fin (s+1)) (f : AnySignature AlgebraicComplex)
    (hf : f ∈ (forest G d hl hN ha hn hp hI i).leaves) :
    f ∈ retained G d hl hN ha hn hp hI := by
  rw [retained,WholeForest.output_labels]
  exact FactorSaturation.leaves_retained (D G d hl hN ha hn hp hI).signature
    (D G d hl hN ha hn hp hI).nonzero i f hf

end Holant.LocalDrafts.Hardness.CyclicRetainedAugmentation
