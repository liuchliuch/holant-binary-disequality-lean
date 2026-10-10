import Holant.Platonic.RankDeficientLocalization.Normalization.MarkedOutputs
import Holant.Certificates.PlatonicDeficient.PivotCoefficients
import Holant.Certificates.AffineEndpoint.Scalars
import Holant.Complexity.FixedGadgetSubstitution.AlgebraicProjectiveAdjoin

/-! Genuine scalar-aware encoded reductions for the unnormalized A.24 input.
The finite field is derived from actual retained entries and the fixed output;
its auxiliary coordinates do not become target vertex labels. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Algebraic Holant.Complexity
open Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Complexity.FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {s : ℕ} {arity : ℕ → ℕ}
variable (signatures : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀i x,IsAlgebraic ℚ (signatures i x))

/-- An actual polynomial Boolean oracle machine with the original target
signature labels, together with the exact source family and physical scale. -/
def EncodedProjectiveNativeAdjoin {m : ℕ} (q : Signature ℂ m) : Prop :=
  ∃ (g : Template) (hg : g.WellFormed s 1 arity) (t : Signature ℂ g.boundary)
    (htalg : ∀x,IsAlgebraic ℚ (t x)), g.boundary=m ∧ HEq t q ∧
    ∃c : ℂ,c≠0 ∧ (OriginalFamily.ambientMacro (retainedCoefficients signatures) g hg).denote=c • t ∧
    ∃p : Fin g.boundary → Bool,t p≠0 ∧
      Nonempty (AlgebraicProjectiveAdjoin.ReductionType (retainedCoefficients signatures)
        (retainedCoefficients_algebraic signatures halg) g hg t htalg p) ∧
      Set.range (fun i : Fin (s+1) =>
        (⟨sourceArity (Adjoin.templates s arity g) i.val,
          PresentedScaledFamily.ambientSource
            (AlgebraicProjectiveAdjoin.values (retainedCoefficients signatures) g t)
            Sum.inl g hg (AlgebraicProjectiveAdjoin.scaleAt (retainedCoefficients signatures)
              (retainedCoefficients_algebraic signatures halg) g hg t htalg p) i⟩ : AnySignature ℂ)) =
        indexedRetainedFamily arity signatures ∪ {⟨m,q⟩}

theorem retained_projective_network_encoded {m : ℕ} (N : Network ℂ m)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (he : ∀e,N.edge e=Signature.disequality) (q : Signature ℂ m)
    (hqalg : ∀x,IsAlgebraic ℚ (q x)) (p : Fin m → Bool) (hp : q p≠0)
    (c : ℂ) (hc : c≠0) (hN : N.denote=c • q) :
    EncodedProjectiveNativeAdjoin signatures halg q := by
  let lab := retainedNetworkLabelling N arity signatures hv
  have hmacro : (OriginalFamily.ambientMacro (retainedCoefficients signatures)
      lab.template lab.wellFormed).denote=c • q :=
    (retainedNetworkLabelling_denote N arity signatures hv he).trans hN
  refine ⟨lab.template,lab.wellFormed,q,hqalg,rfl,HEq.rfl,c,hc,hmacro,p,hp,?_,?_⟩
  · exact ⟨AlgebraicProjectiveAdjoin.reduction (retainedCoefficients signatures)
      (retainedCoefficients_algebraic signatures halg) lab.template lab.wellFormed q hqalg
      c hc hmacro p hp⟩
  · exact AlgebraicProjectiveAdjoin.source_family_exact (retainedCoefficients signatures)
      (retainedCoefficients_algebraic signatures halg) lab.template lab.wellFormed q hqalg
      c hc hmacro p hp

theorem output_algebraic (p : Fin 6) (x : Fin 4 → Bool) :
    IsAlgebraic ℚ (PlatonicDeficient.output p x) := by
  change IsAlgebraic ℚ (OctahedralSeparator.embed _)
  rw [←AffineEndpoint.coe_algebraicEmbed]
  exact (AffineEndpoint.algebraicEmbed _).property.isAlgebraic

theorem primeOutput_algebraic (p : Fin 6) (x : Fin 4 → Bool) :
    IsAlgebraic ℚ (PlatonicDeficient.primeOutput p x) := by
  change IsAlgebraic ℚ (OctahedralSeparator.embed _)
  rw [←AffineEndpoint.coe_algebraicEmbed]
  exact (AffineEndpoint.algebraicEmbed _).property.isAlgebraic

theorem standard_deficient_encoded {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (A : ActualKernelLift Λ D) (g : PlatonicModel)
    (hcomplete : CompleteKernelRepresentatives {K | groupDirection g K} D)
    (h : Signature ℂ 6) (hh : (⟨6,h⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.output p) ∧
      (PlatonicDeficient.support (PlatonicDeficient.output p)).card=10 ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.output p)).rank=3 := by
  obtain ⟨p,N,c,hc0,hN,hv,he,_,_,hs,hR⟩ := standard_deficient_actual_graph A g hcomplete
    (indexedRetainedFamily arity signatures) h hh hb hc hm hr
  exact ⟨p,retained_projective_network_encoded signatures halg N hv he (PlatonicDeficient.output p)
    (output_algebraic p) (PlatonicDeficient.outputPivot p) (PlatonicDeficient.output_pivot_ne_zero p)
    c hc0 hN,hs,hR⟩

theorem prime_deficient_encoded {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
    (A : ActualKernelLift Λ D)
    (hcomplete : CompleteKernelRepresentatives {K | Direction 1 K} D)
    (h : Signature ℂ 6) (hh : (⟨6,h⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hb : ∀K : D,(⟨2,binarySignature (A.binary K)⟩ : AnySignature ℂ)∈indexedRetainedFamily arity signatures)
    (hc : ∀i,MarkedCone 1 (actualMap h (markedRepresentative 1 i)))
    (hm : MixedCards (actualMap h) (markedRepresentative 1))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,EncodedProjectiveNativeAdjoin signatures halg (PlatonicDeficient.primeOutput p) ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.primeOutput p)).rank=3 := by
  obtain ⟨p,N,c,hc0,hN,hv,he,_,_,hR⟩ := prime_deficient_actual_graph A hcomplete
    (indexedRetainedFamily arity signatures) h hh hb hc hm hr
  exact ⟨p,retained_projective_network_encoded signatures halg N hv he (PlatonicDeficient.primeOutput p)
    (primeOutput_algebraic p) (PlatonicDeficient.primeOutputPivot p) (PlatonicDeficient.primeOutput_pivot_ne_zero p)
    c hc0 hN,hR⟩

end
end Holant.Platonic.RankDeficientLocalization.Normalization
