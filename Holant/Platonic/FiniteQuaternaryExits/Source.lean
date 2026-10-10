import Holant.Platonic.FiniteQuaternaryExits.Physical
import Holant.Algebraic.OpenNetwork
import Holant.OpenNetworkComposition.OrdinaryNormalization.Reduction
import Holant.Platonic.RankDeficientLocalization.Normalization.EncodedOutputs

/-! Source Lemma9.8. The finite item is the original normalized quaternary,
and its actual nonzero algebraic realization scalar is explicitly retained.
The finite retained family supplies literal I and actual complete group lifts. -/
namespace Holant.Platonic.FiniteQuaternaryExits
open Holant Holant.Algebraic Holant.Certificates
open Holant.Certificates.PlatonicQuaternaryExits
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.RankDeficientLocalization.Normalization
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (signatures : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀i x,IsAlgebraic ℚ (signatures i x))

include halg in
theorem retained_family_algebraic (t : AnySignature ℂ)
    (ht : t∈indexedRetainedFamily arity signatures) : ∀x,IsAlgebraic ℚ (t.2 x) := by
  obtain ⟨i,rfl⟩ := ht
  exact halg i

/-- All201 marked occurrences, including every normalized rank-four output,
have an actual fixed-family polynomial reduction and an actual terminal graph.
No terminal classification, realization-to-macro, or arithmetic oracle is assumed. -/
theorem source_finite_platonic_quaternary_exits
    (item : PlatonicQuaternaryExits.SourceCase) {D : Set (Kernel ℂ)}
    (A : ActualKernelLift (indexedRetainedFamily arity signatures) D)
    (hcomplete : CompleteKernelRepresentatives {K | item.group K} D)
    (hI : (⟨2,OpenNetworkComposition.OrdinaryNormalization.identitySignature (K:=ℂ)⟩ : AnySignature ℂ)∈
      indexedRetainedFamily arity signatures)
    (c : ℂ) (hc : c≠0) (hcalg : IsAlgebraic ℚ c)
    (hq : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality (c • item.signature)) :
    EncodedProjectiveNativeAdjoin signatures halg item.signature ∧
      ActualExit (indexedRetainedFamily arity signatures) item := by
  have hproj : Gadget.RealizesUpTo (indexedRetainedFamily arity signatures)
      .disequality item.signature := ⟨c,hc,hq⟩
  have hqalg : ∀x,IsAlgebraic ℚ (item.signature x) :=
    projectively_realized_algebraic (retained_family_algebraic signatures halg) c hc hcalg hq
  have hp : ∃p,item.signature p≠0 := by
    by_contra hn
    push_neg at hn
    exact source_signature_nonzero item (funext hn)
  obtain ⟨p,hp⟩ := hp
  obtain ⟨d,hd,N,hv,he,hN⟩ :=
    OpenNetworkComposition.OrdinaryNormalization.realizesUpTo_exists_ordinary hI hproj
  exact ⟨retained_projective_network_encoded signatures halg N hv he item.signature hqalg p hp d hd hN,
    all_cases_actual_exit item A hcomplete hproj⟩
end
end Holant.Platonic.FiniteQuaternaryExits
