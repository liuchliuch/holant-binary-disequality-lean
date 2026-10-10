import Holant.Platonic.RainbowLocalization.PhysicalAssembly

/-! Exact ancestor/kernel occurrence counts and actual source realizability
of the localized graph's vertex labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}
variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {D₀ D₁ D₂ : Presentation ℂ P}

theorem original_arity_ge_six (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n) : 6 ≤ n := by
  have hS := Finset.card_le_univ L.ports
  rw [L.card_ports] at hS
  have hp := Fintype.card_congr p
  simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at hp
  omega

/-- Exactly one vertex has the original ancestor arity; this is the
distinguished original-f occurrence rather than an inferred tensor factor. -/
theorem localization_original_vertex_count (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n) :
    (Finset.univ.filter (fun v : Option (Fin L.common.edges) =>
      (nativeCollectionFinite (originalClosurePorts L p) (effectiveKernels A C) f).arity v = n)).card = 1 := by
  have hn : (2 : ℕ) ≠ n := by have hh := original_arity_ge_six L p; omega
  have he : Finset.univ.filter (fun v : Option (Fin L.common.edges) =>
      (nativeCollectionFinite (originalClosurePorts L p) (effectiveKernels A C) f).arity v = n) = {none} := by
    ext v
    cases v <;> simp [nativeCollectionFinite,collectionArity,hn]
  rw [he]
  simp

/-- The only other vertices are exactly the selected actual binary kernels. -/
theorem localization_binary_vertex_count (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n) :
    (Finset.univ.filter (fun v : Option (Fin L.common.edges) =>
      (nativeCollectionFinite (originalClosurePorts L p) (effectiveKernels A C) f).arity v = 2)).card = (n - 6) / 2 := by
  have hn : n ≠ 2 := by have hh := original_arity_ge_six L p; omega
  have he : Finset.univ.filter (fun v : Option (Fin L.common.edges) =>
      (nativeCollectionFinite (originalClosurePorts L p) (effectiveKernels A C) f).arity v = 2) =
      Finset.univ.erase none := by
    ext v
    cases v <;> simp [nativeCollectionFinite,collectionArity,hn]
  rw [he,Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ,Fintype.card_option,Fintype.card_fin,Nat.add_sub_cancel]
  exact original_kernel_count L p

theorem localization_actual_kernels_safe (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (C : Fin L.common.edges → D)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hD : ∀ K ∈ D, SafeBinary G K) :
    ∀ e, SafeBinary G (A.binary (C e)) := by
  intro e
  rw [← nativePair_effective A C e]
  exact nativePair_safe hG hX (effectiveKernels_safe A C G hG hD e)

/-- After finite enumeration, every graph vertex still has its supplied
actual realization over the same original family. -/
theorem localization_vertices_realizable (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n) (hf : Gadget.Realizes Λ .disequality f) :
    ∀ v, Gadget.Realizes Λ .disequality ((localizationNetwork A L p C f).vertex v) := by
  intro v
  exact actualCollection_vertices_realizable A C (originalClosurePorts L p) f hf
    ((Fintype.equivFin (Option (Fin L.common.edges))).symm v)

theorem localization_vertices_projectively_realizable (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n) (hf : Gadget.Realizes Λ .disequality f) :
    ∀ v, Gadget.RealizesUpTo Λ .disequality ((localizationNetwork A L p C f).vertex v) := by
  intro v
  refine ⟨1,one_ne_zero,?_⟩
  simpa only [one_mul] using localization_vertices_realizable A L p C f hf v

theorem localization_edges_native (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges → D) (f : Signature ℂ n) :
    ∀ e, (localizationNetwork A L p C f).edge e = Signature.disequality := fun _ => rfl

end Holant.Platonic.RainbowLocalization.Physical
