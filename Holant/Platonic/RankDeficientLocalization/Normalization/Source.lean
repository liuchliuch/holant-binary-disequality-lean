import Holant.Platonic.RankDeficientLocalization.Normalization.RealizationSource
import Holant.Platonic.RankDeficientLocalization.Normalization.Geometry
import Holant.OpenNetworkComposition.OrdinaryNormalization.Reduction

/-! A.24 with arbitrary actual input gadgets and actual encoded reductions.
The original finite family contains the available literal I.  Free boundary
stubs are removed by proved ordinary normalization, not assumed absent. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Algebraic Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RainbowLocalization.Physical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (signatures : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀i x,IsAlgebraic ℚ (signatures i x))

abbrev literalIdentity : Signature ℂ 2 := fun x => Signature.equality (x 0) (x 1)

theorem realized_encoded_adjoin {n : ℕ} (h : Signature ℂ n)
    (hI : (⟨2,literalIdentity⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h) :
    EncodedNativeAdjoin signatures halg h := by
  obtain ⟨N,hv,he,hN⟩ := OpenNetworkComposition.OrdinaryNormalization.realizes_exists_ordinary hI hh
  have hred := retained_network_encoded_adjoin signatures halg N hv he
  rwa [hN] at hred

theorem projectively_realized_encoded_adjoin {n : ℕ} (q : Signature ℂ n)
    (hqalg : ∀x,IsAlgebraic ℚ (q x)) (p : Fin n → Bool) (hp : q p≠0)
    (hI : (⟨2,literalIdentity⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hq : Gadget.RealizesUpTo (indexedRetainedFamily arity signatures) .disequality q) :
    EncodedProjectiveNativeAdjoin signatures halg q := by
  obtain ⟨c,hc,N,hv,he,hN⟩ := OpenNetworkComposition.OrdinaryNormalization.realizesUpTo_exists_ordinary hI hq
  exact retained_projective_network_encoded signatures halg N hv he q hqalg p hp c hc hN

/-- Standard-form A.24 under the explicit retained-I condition, including
an arbitrary directly realized ancestor. The q→Λ reduction is constructed
from one composed ordinary macro, so no answer-codec identification is needed. -/
theorem source_A24_standard_with_identity {D : Set (Kernel ℂ)}
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D) (g : PlatonicModel)
    (hcomplete : CompleteKernelRepresentatives {K | groupDirection g K} D)
    (hI : (⟨2,literalIdentity⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (h : Signature ℂ 6)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    Nonempty (RainbowDomainLine (actualMap h) (representative g)) ∧
    Module.finrank ℂ (actualMap h).range=2 ∧ EncodedNativeAdjoin signatures halg h ∧
      ∃p : Fin 6,Gadget.RealizesUpTo (indexedRetainedFamily arity signatures) .disequality
        (PlatonicDeficient.output p) ∧
        EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.output p) ∧
        (PlatonicDeficient.support (PlatonicDeficient.output p)).card=10 ∧
        ∀r : Fin 3,(flatten r (PlatonicDeficient.output p)).rank=3 := by
  obtain ⟨_,_,_,_,_,h2⟩ := standard_deficient_normalization g h hc hm hr
  obtain ⟨p,hq,hs,hR⟩ := standard_deficient_realizesUpTo A g hcomplete h hh hc hm hr
  exact ⟨standard_rainbow g (actualMap h) hc hm,h2,realized_encoded_adjoin signatures halg h hI hh,p,hq,
    projectively_realized_encoded_adjoin signatures halg (PlatonicDeficient.output p)
      (output_algebraic p) (PlatonicDeficient.outputPivot p) (PlatonicDeficient.output_pivot_ne_zero p)
      hI hq,hs,hR⟩

/-- Literal O′ A.24 under the explicit retained-I condition. Physical transport uses
proved current-group matrices, and the derived field changes no target label. -/
theorem source_A24_prime_with_identity {D : Set (Kernel ℂ)}
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D)
    (hcomplete : CompleteKernelRepresentatives {K | Direction 1 K} D)
    (hI : (⟨2,literalIdentity⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (h : Signature ℂ 6)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h)
    (hc : ∀i,MarkedCone 1 (actualMap h (markedRepresentative 1 i)))
    (hm : MixedCards (actualMap h) (markedRepresentative 1))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    Nonempty (RainbowDomainLine (actualMap h) (markedRepresentative 1)) ∧
    Module.finrank ℂ (actualMap h).range=2 ∧ EncodedNativeAdjoin signatures halg h ∧
      ∃p : Fin 6,Gadget.RealizesUpTo (indexedRetainedFamily arity signatures) .disequality
        (PlatonicDeficient.primeOutput p) ∧
        EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.primeOutput p) ∧
        ∀r : Fin 3,(flatten r (PlatonicDeficient.primeOutput p)).rank=3 := by
  obtain ⟨_,_,_,_,_,h2⟩ := marked_deficient_normalization 1 h hc hm hr
  obtain ⟨p,hq,hR⟩ := prime_deficient_realizesUpTo A hcomplete h hh hc hm hr
  exact ⟨marked_rainbow 1 (actualMap h) hc hm,h2,realized_encoded_adjoin signatures halg h hI hh,p,hq,
    projectively_realized_encoded_adjoin signatures halg (PlatonicDeficient.primeOutput p)
      (primeOutput_algebraic p) (PlatonicDeficient.primeOutputPivot p) (PlatonicDeficient.primeOutput_pivot_ne_zero p)
      hI hq,hR⟩

end
end Holant.Platonic.RankDeficientLocalization.Normalization
