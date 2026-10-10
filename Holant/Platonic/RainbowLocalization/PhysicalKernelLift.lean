import Holant.Platonic.RainbowLocalization.PhysicalCommutation

/-! Actual kernel vertices retain the source's normalization scalars.
The normalized effective kernel K is implemented by an actual binary
proportional to X K X through two native-X wires. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure
open scoped BigOperators

structure ActualKernelLift (Λ : SignatureFamily ℂ) (D : Set (Kernel ℂ)) where
  binary : D → Kernel ℂ
  scalar : D → ℂ
  scalar_ne_zero : ∀ K, scalar K ≠ 0
  normalization : ∀ K, binary K = scalar K • nativePair K.val
  actual : ∀ K, Gadget.Realizes Λ .disequality (binarySignature (binary K))

theorem nativePair_smul (c : ℂ) (K : Kernel ℂ) : nativePair (c • K) = c • nativePair K := by
  ext a b
  change nativePair (c • K) a b = c * nativePair K a b
  rw [nativePair_apply,nativePair_apply]
  rfl

variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {E : Type*} [Fintype E] [DecidableEq E]

def effectiveKernels (A : ActualKernelLift Λ D) (C : E → D) : E → Kernel ℂ :=
  fun e => A.scalar (C e) • (C e).val

def realizationScale (A : ActualKernelLift Λ D) (C : E → D) : ℂ := ∏ e, A.scalar (C e)

theorem realizationScale_ne_zero (A : ActualKernelLift Λ D) (C : E → D) :
    realizationScale A C ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun e _ => A.scalar_ne_zero (C e))

/-- The graph's binary labels are exactly the stored actual representatives. -/
theorem nativePair_effective (A : ActualKernelLift Λ D) (C : E → D) (e : E) :
    nativePair (effectiveKernels A C e) = A.binary (C e) := by
  rw [effectiveKernels,nativePair_smul,A.normalization]

theorem effectiveKernels_safe (A : ActualKernelLift Λ D) (C : E → D)
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hD : ∀ K ∈ D, SafeBinary G K) : ∀ e, SafeBinary G (effectiveKernels A C e) := by
  intro e
  exact SafeBinary.scale hG (hD _ (C e).property) (A.scalar_ne_zero (C e))

theorem kernelProduct_effective (A : ActualKernelLift Λ D) (C : E → D)
    (y : E → Bool × Bool) :
    kernelProduct (effectiveKernels A C) y = realizationScale A C * kernelProduct (fun e => (C e).val) y := by
  simp only [kernelProduct,effectiveKernels,realizationScale,Pi.smul_apply,smul_eq_mul,
    Finset.prod_mul_distrib]

/-- Every actual representative's nonzero normalization coefficient is
retained in the complete contraction, including the empty collection. -/
theorem contractCollection_effective {P Q : Type*} [DecidableEq P]
    (A : ActualKernelLift Λ D) (C : E → D) (p : CollectionPorts P Q E) (f : Tensor ℂ P) :
    contractCollection p (effectiveKernels A C) f =
      realizationScale A C • contractCollection p (fun e => (C e).val) f := by
  funext x
  simp only [contractCollection,kernelProduct_effective,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

def actualCollectionNetwork {m n : ℕ} (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m) : Network ℂ n :=
  nativeCollectionNetwork p (effectiveKernels A C) f

theorem actualCollection_denote {m n : ℕ} (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m) :
    (actualCollectionNetwork A C p f).denote =
      realizationScale A C • contractCollection p (fun e => (C e).val) f := by
  rw [actualCollectionNetwork,nativeCollection_denote,contractCollection_effective]

theorem actualCollection_vertices {m n : ℕ} (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m) :
    (actualCollectionNetwork A C p f).shape.vertices = Fintype.card E + 1 :=
  nativeCollection_vertices p (effectiveKernels A C) f

theorem actualCollection_edges {m n : ℕ} (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m) :
    (actualCollectionNetwork A C p f).shape.edges = 2 * Fintype.card E :=
  nativeCollection_edges p (effectiveKernels A C) f

/-- The finite graph contains one original f-labelled vertex; every other
vertex is one of the actual binary representatives with its recorded ports. -/
theorem actualCollection_vertex_labels {m n : ℕ} (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m) :
    (nativeCollectionFinite p (effectiveKernels A C) f).vertex none = f ∧
      ∀ e, (nativeCollectionFinite p (effectiveKernels A C) f).vertex (some e) =
        binarySignature (A.binary (C e)) := by
  refine ⟨rfl,?_⟩
  intro e
  change binarySignature (nativePair (effectiveKernels A C e)) = _
  rw [nativePair_effective]

/-- Every individual graph vertex is genuinely realizable over the retained
source family.  This does not by itself assert arbitrary gadget substitution. -/
theorem actualCollection_vertices_realizable {m n : ℕ} (A : ActualKernelLift Λ D) (C : E → D)
    (p : CollectionPorts (Fin m) (Fin n) E) (f : Signature ℂ m)
    (hf : Gadget.Realizes Λ .disequality f) :
    ∀ v : Option E, Gadget.Realizes Λ .disequality
      ((nativeCollectionFinite p (effectiveKernels A C) f).vertex v) := by
  intro v
  cases v with
  | none => exact hf
  | some e =>
    rw [(actualCollection_vertex_labels A C p f).2 e]
    exact A.actual (C e)

end Holant.Platonic.RainbowLocalization.Physical
