import Holant.Proofs.Reductions.CyclicPowerConsumer.StableSuccessor
import Holant.Proofs.Reductions.FactorSaturation.OriginalCodec


noncomputable section
namespace Holant.LocalDrafts.Hardness.CyclicRetainedAugmentation
open Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant.LocalDrafts.FinitePGL2.Stabilization
open GeneralExtraction FactorSaturation
open scoped BigOperators

variable {s N : ℕ} {a : ℕ → ℕ} {F : SignatureFamily ℂ}
variable {R : PhysicalAttachments.Representatives F N} {q : Signature ℂ 4}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (d : CountedDoubled R q)
variable (hl : ∀ v, (⟨d.certificate.circuit.network.shape.arity v,
  d.certificate.circuit.network.vertex v⟩ : AnySignature ℂ) ∈
    mapFamily inclusion (CyclicPowerConsumer.family G))
variable (hN : 0 < N) (ha : a s = 2)

abbrev binary := CyclicPowerConsumer.machineFactor G d hl hN ha
abbrev adjoined := RetainedPairReduction.extended G (binary G d hl hN ha)
def rootSignature (i : Fin (s+1)) : AnySignature AlgebraicComplex :=
  ⟨a i.val,adjoined G d hl hN ha i⟩

theorem old_label (i : Fin s) : rootSignature G d hl hN ha ⟨i.val,by omega⟩ =
    (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex) := by
  unfold rootSignature adjoined RetainedPairReduction.extended
  rw [GeneralOriginalQuery.source_old]

theorem sigma_cast {m n : ℕ} (h : m = n) (f : Signature AlgebraicComplex m) :
    (⟨n,CyclicPowerConsumer.castFactor h f⟩ : AnySignature AlgebraicComplex) = ⟨m,f⟩ := by
  cases h
  rfl

theorem new_label : rootSignature G d hl hN ha ⟨s,by omega⟩ =
    (⟨2,CyclicPowerConsumer.factor G d hl hN⟩ : AnySignature AlgebraicComplex) := by
  unfold rootSignature adjoined RetainedPairReduction.extended
  rw [GeneralOriginalQuery.source_new]
  exact sigma_cast ha.symm _

theorem root_range : Set.range (rootSignature G d hl hN ha) =
    CyclicPowerConsumer.family G ∪ {⟨2,CyclicPowerConsumer.factor G d hl hN⟩} := by
  change Set.range (fun i => (⟨a i.val,
    GeneralExtraction.RetainedPairReduction.extended G (binary G d hl hN ha) i⟩ :
      AnySignature AlgebraicComplex)) = _
  rw [RetainedPairReduction.extended,GeneralOriginalQuery.source_family_exact]
  rw [show (⟨a s,binary G d hl hN ha⟩ : AnySignature AlgebraicComplex) =
    ⟨2,CyclicPowerConsumer.factor G d hl hN⟩ from sigma_cast ha.symm _]
  rfl

theorem binary_nonzero : binary G d hl hN ha ≠ 0 := by
  have transport {m n : ℕ} (h : m = n) (f : Signature AlgebraicComplex m)
      (hf : f ≠ 0) : CyclicPowerConsumer.castFactor h f ≠ 0 := by
    cases h
    exact hf
  exact transport ha.symm _ (CyclicPowerConsumer.factor_nonzero G d hl hN)

variable (hn : ∀ i, G i ≠ 0) (hp : ∀ i : Fin s, 0 < a i.val)
variable (hI : RetainsIdentity (CyclicPowerConsumer.family G))

include hn in
theorem root_nonzero (i : Fin (s+1)) : (rootSignature G d hl hN ha i).2 ≠ 0 := by
  by_cases hi : i.val < s
  · have he : i = ⟨(⟨i.val,hi⟩ : Fin s).val,by omega⟩ := Fin.ext rfl
    rw [he,old_label]
    exact hn _
  · have he : i = ⟨s,by omega⟩ := by
      apply Fin.ext
      change i.val = s
      have := i.isLt
      omega
    rw [he,new_label]
    exact CyclicPowerConsumer.factor_nonzero G d hl hN

include hp in
theorem root_positive (i : Fin (s+1)) : 0 < (rootSignature G d hl hN ha i).1 := by
  by_cases hi : i.val < s
  · exact hp ⟨i.val,hi⟩
  · have he : i.val = s := by omega
    change 0 < a i.val
    rw [he,ha]
    decide

def roots : WholeForest.Roots (s+1) where
  signature := rootSignature G d hl hN ha
  nonzero := root_nonzero G d hl hN ha hn
  positive := root_positive G d hl hN ha hp
  identity := by
    rw [root_range]
    exact Set.subset_union_left hI

end Holant.LocalDrafts.Hardness.CyclicRetainedAugmentation
