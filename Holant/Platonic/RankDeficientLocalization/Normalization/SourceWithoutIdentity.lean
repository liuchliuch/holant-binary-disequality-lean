import Holant.Platonic.RankDeficientLocalization.Normalization.Source
import Holant.Platonic.RankDeficientLocalization.Normalization.AncestorNoFactors
import Holant.OpenNetworkComposition.FactorFreeNormalization.Reduction
import Holant.OpenNetworkComposition.FactorFreeNormalization.QuaternaryRanks

/-! Bare-Λ A.24. Actual pair-cut minor certificates exclude free/free boundary
components for h; the output ranks333 exclude them for q and q′. Ordinary
normalization therefore needs no added identity label or family enlargement. -/
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

theorem realized_encoded_adjoin_without_identity {n : ℕ} (h : Signature ℂ n)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h)
    (hf : NoXFactor h) : EncodedNativeAdjoin signatures halg h := by
  obtain ⟨N,hv,he,hN⟩ := OpenNetworkComposition.FactorFreeNormalization.realizes_exists_ordinary hh hf
  have hred := retained_network_encoded_adjoin signatures halg N hv he
  rwa [hN] at hred

theorem projectively_realized_encoded_without_identity {n : ℕ} (q : Signature ℂ n)
    (hqalg : ∀x,IsAlgebraic ℚ (q x)) (p : Fin n → Bool) (hp : q p≠0)
    (hq : Gadget.RealizesUpTo (indexedRetainedFamily arity signatures) .disequality q)
    (hf : NoXFactor q) : EncodedProjectiveNativeAdjoin signatures halg q := by
  obtain ⟨c,hc,N,hv,he,hN⟩ := OpenNetworkComposition.FactorFreeNormalization.realizesUpTo_exists_ordinary hq hf
  exact retained_projective_network_encoded signatures halg N hv he q hqalg p hp c hc hN

/-- Complete standard T/O/I A.24 on the original finite algebraic Λ.
Both actual realization and encoded reduction start from arbitrary input
gadgets; neither I membership nor an ordinary-macro premise is assumed. -/
theorem source_A24_standard {D : Set (Kernel ℂ)}
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
        EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.output p) ∧
        (PlatonicDeficient.support (PlatonicDeficient.output p)).card=10 ∧
        ∀r : Fin 3,(flatten r (PlatonicDeficient.output p)).rank=3 := by
  obtain ⟨_,_,_,_,_,h2⟩ := standard_deficient_normalization g h hc hm hr
  obtain ⟨p,hq,hs,hR⟩ := standard_deficient_realizesUpTo A g hcomplete h hh hc hm hr
  have hnf := standard_ancestor_noXFactor g h hc hm hr
  have hqnf := noXFactor_of_threeRanks (PlatonicDeficient.output p) (fun r => by rw [hR r]; norm_num)
  exact ⟨standard_rainbow g (actualMap h) hc hm,h2,
    realized_encoded_adjoin_without_identity signatures halg h hh hnf,p,hq,
    projectively_realized_encoded_without_identity signatures halg (PlatonicDeficient.output p)
      (output_algebraic p) (PlatonicDeficient.outputPivot p) (PlatonicDeficient.output_pivot_ne_zero p)
      hq hqnf,hs,hR⟩

/-- Complete A.24 in the literal current O′ coordinates, with no support-ten
claim transported and no identity or similarity added to the original family. -/
theorem source_A24_prime {D : Set (Kernel ℂ)}
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
        EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.primeOutput p) ∧
        ∀r : Fin 3,(flatten r (PlatonicDeficient.primeOutput p)).rank=3 := by
  obtain ⟨_,_,_,_,_,h2⟩ := marked_deficient_normalization 1 h hc hm hr
  obtain ⟨p,hq,hR⟩ := prime_deficient_realizesUpTo A hcomplete h hh hc hm hr
  have hnf := marked_ancestor_noXFactor 1 h hc hm hr
  have hqnf := noXFactor_of_threeRanks (PlatonicDeficient.primeOutput p) (fun r => by rw [hR r]; norm_num)
  exact ⟨marked_rainbow 1 (actualMap h) hc hm,h2,
    realized_encoded_adjoin_without_identity signatures halg h hh hnf,p,hq,
    projectively_realized_encoded_without_identity signatures halg (PlatonicDeficient.primeOutput p)
      (primeOutput_algebraic p) (PlatonicDeficient.primeOutputPivot p) (PlatonicDeficient.primeOutput_pivot_ne_zero p)
      hq hqnf,hR⟩

end
end Holant.Platonic.RankDeficientLocalization.Normalization
