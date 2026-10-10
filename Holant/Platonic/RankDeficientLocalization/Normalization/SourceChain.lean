import Holant.Platonic.RankDeficientLocalization.Normalization.AdjoinedFamily

/-! The literal displayed A.24 chain q→(Λ,h)→Λ, alongside the independently
constructed stronger direct q→Λ reduction. Each arrow has its own honest
fixed-field representation; no answer-codec composition is asserted. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Algebraic Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RainbowLocalization.Physical
open Holant.OpenNetworkComposition.FactorFreeNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (signatures : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀i x,IsAlgebraic ℚ (signatures i x))

theorem source_A24_standard_chain {D : Set (Kernel ℂ)}
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D) (g : PlatonicModel)
    (hcomplete : CompleteKernelRepresentatives {K | groupDirection g K} D)
    (h : Signature ℂ 6)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    Nonempty (RainbowDomainLine (actualMap h) (representative g)) ∧
    Module.finrank ℂ (actualMap h).range=2 ∧ EncodedNativeAdjoin signatures halg h ∧
      ∃p : Fin 6,Gadget.RealizesUpTo (indexedRetainedFamily arity signatures) .disequality
        (PlatonicDeficient.output p) ∧
        EncodedProjectiveNativeAdjoin (adjoinedSignatures signatures h)
          (adjoined_algebraic signatures halg h hh) (PlatonicDeficient.output p) ∧
        EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.output p) ∧
        (PlatonicDeficient.support (PlatonicDeficient.output p)).card=10 ∧
        ∀r : Fin 3,(flatten r (PlatonicDeficient.output p)).rank=3 := by
  obtain ⟨R,h2,hred,p,hq,hqred,hs,hR⟩ := source_A24_standard signatures halg A g hcomplete h hh hc hm hr
  refine ⟨R,h2,hred,p,hq,?_,hqred,hs,hR⟩
  exact realized_adjoined_access signatures halg h hh (PlatonicDeficient.output p)
    (output_algebraic p) (PlatonicDeficient.outputPivot p) (PlatonicDeficient.output_pivot_ne_zero p) hq
    (noXFactor_of_threeRanks _ (fun r => by rw [hR r]; norm_num))

theorem source_A24_prime_chain {D : Set (Kernel ℂ)}
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D)
    (hcomplete : CompleteKernelRepresentatives {K | Direction 1 K} D)
    (h : Signature ℂ 6)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h)
    (hc : ∀i,MarkedCone 1 (actualMap h (markedRepresentative 1 i)))
    (hm : MixedCards (actualMap h) (markedRepresentative 1))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    Nonempty (RainbowDomainLine (actualMap h) (markedRepresentative 1)) ∧
    Module.finrank ℂ (actualMap h).range=2 ∧ EncodedNativeAdjoin signatures halg h ∧
      ∃p : Fin 6,Gadget.RealizesUpTo (indexedRetainedFamily arity signatures) .disequality
        (PlatonicDeficient.primeOutput p) ∧
        EncodedProjectiveNativeAdjoin (adjoinedSignatures signatures h)
          (adjoined_algebraic signatures halg h hh) (PlatonicDeficient.primeOutput p) ∧
        EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.primeOutput p) ∧
        ∀r : Fin 3,(flatten r (PlatonicDeficient.primeOutput p)).rank=3 := by
  obtain ⟨R,h2,hred,p,hq,hqred,hR⟩ := source_A24_prime signatures halg A hcomplete h hh hc hm hr
  refine ⟨R,h2,hred,p,hq,?_,hqred,hR⟩
  exact realized_adjoined_access signatures halg h hh (PlatonicDeficient.primeOutput p)
    (primeOutput_algebraic p) (PlatonicDeficient.primeOutputPivot p) (PlatonicDeficient.primeOutput_pivot_ne_zero p) hq
    (noXFactor_of_threeRanks _ (fun r => by rw [hR r]; norm_num))

end
end Holant.Platonic.RankDeficientLocalization.Normalization
