import Holant.Platonic.RainbowLocalization.PhysicalAssembly
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! Literal finite-family labels for the physical localization graph.  Membership
of the original signature and the stored actual binary representatives suffices;
the constructor chooses all indices and proves the exact ordinary macro value.
No claim that an arbitrary open-network realization is ordinary is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Complexity.FixedGadgetSubstitution

/-- The literal signatures available in a fixed finite indexed family. -/
def indexedRetainedFamily {K : Type*} {s : ℕ} (arity : ℕ → ℕ)
    (signatures : (i : Fin s) → Signature K (arity i.val)) : SignatureFamily K :=
  Set.range (fun i => (⟨arity i.val, signatures i⟩ : AnySignature K))

private theorem signature_apply_of_sigma_eq {K : Type*} {m n : ℕ}
    {f : Signature K m} {g : Signature K n}
    (h : (⟨m,f⟩ : AnySignature K) = ⟨n,g⟩) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast (congrArg Sigma.fst h) i)) = g x := by
  cases h
  rfl

section Ordinary
variable {K : Type*} {n s : ℕ} (N : Network K n) (arity : ℕ → ℕ)
variable (signatures : (i : Fin s) → Signature K (arity i.val))
variable (hv : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature K) ∈
  indexedRetainedFamily arity signatures)

/-- Choose literal source indices, retaining the given graph's complete shape.
There is exactly one permitted edge label, the native disequality table. -/
def retainedNetworkLabelling : Labelling N.shape s 1 arity where
  vertex v := Classical.choose (hv v)
  vertex_arity v := congrArg Sigma.fst (Classical.choose_spec (hv v))
  edge _ := 0

@[simp] theorem retainedNetworkLabelling_edge (e : Fin N.shape.edges) :
    (retainedNetworkLabelling N arity signatures hv).edge e = 0 := rfl

theorem retainedNetworkLabelling_label (v : Fin N.shape.vertices) :
    (⟨arity ((retainedNetworkLabelling N arity signatures hv).vertex v).val,
      signatures ((retainedNetworkLabelling N arity signatures hv).vertex v)⟩ : AnySignature K) =
        ⟨N.shape.arity v,N.vertex v⟩ := Classical.choose_spec (hv v)

theorem retainedNetworkLabelling_vertex [CommSemiring K] (v : Fin N.shape.vertices)
    (x : Fin (N.shape.arity v) → Bool) :
    ((retainedNetworkLabelling N arity signatures hv).sourceNetwork signatures
      (fun _ : Fin 1 => Signature.disequality)).vertex v x = N.vertex v x := by
  exact signature_apply_of_sigma_eq (Classical.choose_spec (hv v)) x

/-- Literal family membership and literal native edges recover the same graph,
not just its projective value. -/
theorem retainedNetworkLabelling_sourceNetwork [CommSemiring K]
    (he : ∀ e, N.edge e = Signature.disequality) :
    (retainedNetworkLabelling N arity signatures hv).sourceNetwork signatures
      (fun _ : Fin 1 => Signature.disequality) = N := by
  change Network.mk N.shape _ _ = Network.mk N.shape N.vertex N.edge
  congr 1
  · funext v x
    exact signature_apply_of_sigma_eq (Classical.choose_spec (hv v)) x
  · funext e
    exact (he e).symm

theorem retainedNetworkLabelling_denote [CommSemiring K]
    (he : ∀ e, N.edge e = Signature.disequality) :
    let lab := retainedNetworkLabelling N arity signatures hv
    (lab.template.network lab.wellFormed signatures
      (fun _ : Fin 1 => Signature.disequality)).denote = N.denote := by
  dsimp only
  rw [Labelling.denote_template,retainedNetworkLabelling_sourceNetwork N arity signatures hv he]

end Ordinary

variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {E : Type*} [Fintype E] [DecidableEq E] {m n s : ℕ}

/-- Every physical vertex is literally in the indexed retained family.  The
binary hypothesis names `A.binary`, including its normalization coefficient. -/
theorem actualCollection_retained_vertices
    (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m)
    (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (hf : (⟨m,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hb : ∀ K : D, (⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    ∀ v, (⟨(actualCollectionNetwork A C p f).shape.arity v,
      (actualCollectionNetwork A C p f).vertex v⟩ : AnySignature ℂ) ∈
        indexedRetainedFamily arity signatures := by
  intro v
  change (⟨collectionArity m ((Fintype.equivFin (Option E)).symm v),
    nativeCollectionLabels f (effectiveKernels A C) ((Fintype.equivFin (Option E)).symm v)⟩ :
      AnySignature ℂ) ∈ indexedRetainedFamily arity signatures
  cases h : (Fintype.equivFin (Option E)).symm v with
  | none => exact hf
  | some e =>
    change (⟨2,binarySignature (nativePair (effectiveKernels A C e))⟩ : AnySignature ℂ) ∈ _
    rw [nativePair_effective]
    exact hb (C e)

/-- A completely constructed ordinary macro for any actual collection graph. -/
def actualCollectionRetainedLabelling
    (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m)
    (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (hf : (⟨m,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hb : ∀ K : D, (⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    Labelling (actualCollectionNetwork A C p f).shape s 1 arity :=
  retainedNetworkLabelling _ arity signatures
    (actualCollection_retained_vertices A C p f arity signatures hf hb)

section LiteralIndices
variable (A : ActualKernelLift Λ D) (C : E → D)
variable (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m)
variable (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature ℂ (arity i.val))
variable (hf : (⟨m,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
variable (hb : ∀ K : D, (⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
  indexedRetainedFamily arity signatures)

/-- The chosen original index has exactly the original arity and signature. -/
theorem actualCollectionRetainedLabelling_original_label :
    let lab := actualCollectionRetainedLabelling A C p f arity signatures hf hb
    let i := lab.vertex ((Fintype.equivFin (Option E)) none)
    (⟨arity i.val,signatures i⟩ : AnySignature ℂ) = ⟨m,f⟩ := by
  have h := retainedNetworkLabelling_label (actualCollectionNetwork A C p f) arity signatures
    (actualCollection_retained_vertices A C p f arity signatures hf hb)
    ((Fintype.equivFin (Option E)) none)
  refine h.trans ?_
  change (⟨collectionArity m ((Fintype.equivFin (Option E)).symm
    ((Fintype.equivFin (Option E)) none)),nativeCollectionLabels f (effectiveKernels A C)
    ((Fintype.equivFin (Option E)).symm ((Fintype.equivFin (Option E)) none))⟩ : AnySignature ℂ) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Each other chosen index is the literal stored actual binary, with arity two. -/
theorem actualCollectionRetainedLabelling_binary_label (e : E) :
    let lab := actualCollectionRetainedLabelling A C p f arity signatures hf hb
    let i := lab.vertex ((Fintype.equivFin (Option E)) (some e))
    (⟨arity i.val,signatures i⟩ : AnySignature ℂ) = ⟨2,binarySignature (A.binary (C e))⟩ := by
  have h := retainedNetworkLabelling_label (actualCollectionNetwork A C p f) arity signatures
    (actualCollection_retained_vertices A C p f arity signatures hf hb)
    ((Fintype.equivFin (Option E)) (some e))
  refine h.trans ?_
  change (⟨collectionArity m ((Fintype.equivFin (Option E)).symm
    ((Fintype.equivFin (Option E)) (some e))),nativeCollectionLabels f (effectiveKernels A C)
    ((Fintype.equivFin (Option E)).symm ((Fintype.equivFin (Option E)) (some e)))⟩ : AnySignature ℂ) = _
  rw [Equiv.symm_apply_apply]
  change (⟨2,binarySignature (nativePair (effectiveKernels A C e))⟩ : AnySignature ℂ) = _
  rw [nativePair_effective]

end LiteralIndices

theorem actualCollectionRetainedLabelling_sourceNetwork
    (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m)
    (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (hf : (⟨m,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hb : ∀ K : D, (⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    (actualCollectionRetainedLabelling A C p f arity signatures hf hb).sourceNetwork
      signatures (fun _ : Fin 1 => Signature.disequality) = actualCollectionNetwork A C p f :=
  retainedNetworkLabelling_sourceNetwork _ arity signatures _ (fun _ => rfl)

theorem actualCollectionRetainedLabelling_denote
    (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m)
    (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (hf : (⟨m,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hb : ∀ K : D, (⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    let lab := actualCollectionRetainedLabelling A C p f arity signatures hf hb
    (lab.template.network lab.wellFormed signatures
      (fun _ : Fin 1 => Signature.disequality)).denote = (actualCollectionNetwork A C p f).denote :=
  retainedNetworkLabelling_denote _ arity signatures _ (fun _ => rfl)

section Localization
variable {P : Type*} [Fintype P] [DecidableEq P]
variable {D₀ D₁ D₂ : Presentation ℂ P}
variable (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
variable (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n)
variable (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature ℂ (arity i.val))
variable (hf : (⟨n,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
variable (hb : ∀ K : D, (⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
  indexedRetainedFamily arity signatures)

/-- The physical source-9.9 graph, labelled only by retained input signatures. -/
def localizationRetainedLabelling : Labelling (localizationNetwork A L p C f).shape s 1 arity :=
  actualCollectionRetainedLabelling A C (originalClosurePorts L p) f arity signatures hf hb

theorem localizationRetainedLabelling_sourceNetwork :
    (localizationRetainedLabelling A L p C f arity signatures hf hb).sourceNetwork
      signatures (fun _ : Fin 1 => Signature.disequality) = localizationNetwork A L p C f :=
  actualCollectionRetainedLabelling_sourceNetwork A C (originalClosurePorts L p) f
    arity signatures hf hb

@[simp] theorem localizationRetainedLabelling_edge
    (e : Fin (localizationNetwork A L p C f).shape.edges) :
    (localizationRetainedLabelling A L p C f arity signatures hf hb).edge e = 0 := rfl

/-- The single edge-table entry is the literal native X kernel. -/
theorem localizationRetainedLabelling_native_edges
    (e : Fin (localizationNetwork A L p C f).shape.edges) :
    ((localizationRetainedLabelling A L p C f arity signatures hf hb).sourceNetwork
      signatures (fun _ : Fin 1 => Signature.disequality)).edge e = (X : Kernel ℂ) := rfl

@[simp] theorem localizationRetainedLabelling_boundary :
    (localizationRetainedLabelling A L p C f arity signatures hf hb).template.boundary = 6 := rfl

theorem localizationRetainedLabelling_denote :
    let lab := localizationRetainedLabelling A L p C f arity signatures hf hb
    (lab.template.network lab.wellFormed signatures
      (fun _ : Fin 1 => Signature.disequality)).denote = localizationSignature A L p C f :=
  actualCollectionRetainedLabelling_denote A C (originalClosurePorts L p) f
    arity signatures hf hb

theorem localizationRetainedLabelling_vertices :
    (localizationRetainedLabelling A L p C f arity signatures hf hb).template.vertices.length =
      (n - 6) / 2 + 1 := by
  rw [Labelling.vertices_length,localization_vertices]

theorem localizationRetainedLabelling_edges :
    (localizationRetainedLabelling A L p C f arity signatures hf hb).template.edges.length =
      2 * ((n - 6) / 2) := by
  rw [Labelling.edges_length,localization_edges]

end Localization
end Holant.Platonic.RainbowLocalization.Physical
