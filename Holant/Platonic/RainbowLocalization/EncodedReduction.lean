import Holant.Platonic.RainbowLocalization.RetainedLabels
import Holant.Complexity.FixedGadgetSubstitution.OriginalFamily

/-! Literal finite retained-family labels construct the source9.9 macro and its
actual encoded oracle reduction. All fixed coefficients determine one common
number field before graph inputs; no realization-to-ordinary-graph premise is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Algebraic Holant.Complexity
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {arity : ℕ → ℕ}
variable (signatures : (i : Fin s) → Signature ℂ (arity i.val))

def retainedCoefficients : ExactSignatureTables.CoefficientIndex s 1 arity → ℂ
  | .inl ⟨i,x⟩ => signatures i x
  | .inr (_,a,b) => Signature.disequality a b

 theorem retainedCoefficients_algebraic
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x)) :
    ∀a,IsAlgebraic ℚ (retainedCoefficients signatures a) := by
  intro a
  rcases a with ⟨i,x⟩ | ⟨i,a,b⟩
  · exact halg i x
  · cases a <;> cases b <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

/-- This predicate contains an actual polynomial Boolean oracle machine,
faithful graph/field codecs and exact equality to the stated physical output. -/
def EncodedNativeAdjoin {m : ℕ}
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x)) (h : Signature ℂ m) : Prop :=
  ∃ (g : Template) (hg : g.WellFormed s 1 arity),
    g.boundary=m ∧
    HEq (OriginalFamily.ambientMacro (retainedCoefficients signatures) g hg).denote h ∧
    Nonempty (OriginalFamily.ReductionType (retainedCoefficients signatures)
      (retainedCoefficients_algebraic signatures halg) g hg)

/-- The ordinary graph is labelled constructively using original membership.
The queried family is exactly the old family and the displayed new tensor. -/
theorem retained_network_encoded_adjoin {m : ℕ}
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x)) (N : Network ℂ m)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (he : ∀e,N.edge e=Signature.disequality) :
    EncodedNativeAdjoin signatures halg N.denote := by
  let lab := retainedNetworkLabelling N arity signatures hv
  refine ⟨lab.template,lab.wellFormed,rfl,?_,?_⟩
  · apply heq_of_eq
    exact retainedNetworkLabelling_denote N arity signatures hv he
  · exact ⟨OriginalFamily.reduction (retainedCoefficients signatures)
      (retainedCoefficients_algebraic signatures halg) lab.template lab.wellFormed⟩

variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}
variable {D₀ D₁ D₂ : Presentation ℂ P}

/-- Source9.9's specific one-ancestor graph uses literal stored binaries. Their
recorded normalization coefficients are already part of those vertex entries. -/
theorem localization_encoded_adjoin
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x))
    (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) (C : Fin L.common.edges → D) (f : Signature ℂ n)
    (hf : (⟨n,f⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    EncodedNativeAdjoin signatures halg (localizationSignature A L p C f) :=
  retained_network_encoded_adjoin signatures halg (localizationNetwork A L p C f)
    (actualCollection_retained_vertices A C (originalClosurePorts L p) f arity signatures hf hb)
    (fun _ => rfl)

end Holant.Platonic.RainbowLocalization.Physical
