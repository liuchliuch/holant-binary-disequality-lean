import Holant.Platonic.RankDeficientLocalization.Normalization.EncodedOutputs
import Holant.OpenNetworkComposition.ProjectiveSubstitution

/-! A.24's actual input is a directly realized h, not a supplied ordinary
macro.  Actual binary and ancestor gadgets are genuinely substituted here. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RainbowLocalization.Physical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}

def storedResources (A : ActualKernelLift Λ D) (h : Signature ℂ 6) : SignatureFamily ℂ :=
  {t | t=⟨6,h⟩ ∨ ∃K : D,t=⟨2,binarySignature (A.binary K)⟩}

theorem storedResources_realizes (A : ActualKernelLift Λ D) (h : Signature ℂ 6)
    (hh : Gadget.Realizes Λ .disequality h) (t : AnySignature ℂ)
    (ht : t∈storedResources A h) : Gadget.Realizes Λ .disequality t.2 := by
  rcases ht with rfl|⟨K,rfl⟩
  · exact hh
  · exact A.actual K

theorem actual_graph_realizesUpTo (A : ActualKernelLift Λ D) (h : Signature ℂ 6)
    (hh : Gadget.Realizes Λ .disequality h) {n : ℕ} (N : Network ℂ n)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈storedResources A h)
    (he : ∀e,N.edge e=Signature.disequality) (q : Signature ℂ n) (c : ℂ) (hc : c≠0)
    (hN : N.denote=c • q) : Gadget.RealizesUpTo Λ .disequality q := by
  obtain ⟨d,hd,hreal⟩ := OpenNetworkComposition.realizes_network_upTo Λ N
    (fun v => storedResources_realizes A h hh _ (hv v)) he (by norm_num)
  refine ⟨d*c,mul_ne_zero hd hc,?_⟩
  change Gadget.Realizes Λ .disequality (d • N.denote) at hreal
  rw [hN,smul_smul] at hreal
  exact hreal

/-- Standard A.24 directly realizes its literal qπ over the original Λ.
The arbitrary input gadgets and any wire-circle scale are preserved. -/
theorem standard_deficient_realizesUpTo (A : ActualKernelLift Λ D) (g : PlatonicModel)
    (hcomplete : CompleteKernelRepresentatives {K | groupDirection g K} D)
    (h : Signature ℂ 6) (hh : Gadget.Realizes Λ .disequality h)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,Gadget.RealizesUpTo Λ .disequality (PlatonicDeficient.output p) ∧
      (PlatonicDeficient.support (PlatonicDeficient.output p)).card=10 ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.output p)).rank=3 := by
  obtain ⟨p,N,c,hc0,hN,hv,he,_,_,hs,hR⟩ := standard_deficient_actual_graph A g hcomplete
    (storedResources A h) h (Or.inl rfl) (fun K => Or.inr ⟨K,rfl⟩) hc hm hr
  exact ⟨p,actual_graph_realizesUpTo A h hh N hv he _ c hc0 hN,hs,hR⟩

/-- Literal O′ A.24 directly realizes q′π over the original Λ, through the
proved current-group graph and actual-gadget substitution. -/
theorem prime_deficient_realizesUpTo (A : ActualKernelLift Λ D)
    (hcomplete : CompleteKernelRepresentatives {K | Direction 1 K} D)
    (h : Signature ℂ 6) (hh : Gadget.Realizes Λ .disequality h)
    (hc : ∀i,MarkedCone 1 (actualMap h (markedRepresentative 1 i)))
    (hm : MixedCards (actualMap h) (markedRepresentative 1))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,Gadget.RealizesUpTo Λ .disequality (PlatonicDeficient.primeOutput p) ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.primeOutput p)).rank=3 := by
  obtain ⟨p,N,c,hc0,hN,hv,he,_,_,hR⟩ := prime_deficient_actual_graph A hcomplete
    (storedResources A h) h (Or.inl rfl) (fun K => Or.inr ⟨K,rfl⟩) hc hm hr
  exact ⟨p,actual_graph_realizesUpTo A h hh N hv he _ c hc0 hN,hR⟩

end
end Holant.Platonic.RankDeficientLocalization.Normalization
