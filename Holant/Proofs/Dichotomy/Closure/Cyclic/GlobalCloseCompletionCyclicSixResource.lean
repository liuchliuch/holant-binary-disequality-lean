import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicHigherStructure
import Holant.ReedMuller.WeightTwoIntegration.NativeSource

/-! A six-port prime with the actual I/X-span matching deck produces the
literal even-four source using two original copies and retained identities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicSixResource
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas
open GlobalCloseCompletionCyclicHigherDeck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable (G : Set (Binary (K:=ℂ))) (group : ProjectiveMatrixGroup G)
variable (span : ∀T∈G,∃a b : ℂ,T=fun u v=>a*Signature.equality u v+b*Signature.disequality u v)
variable (f : Signature ℂ 6) (prime : Prime (⟨6,f⟩ : AnySignature ℂ)) (safe : Deck G f)
include group span prime safe in
theorem live_weight_graph : ∃u v,(weightGraph (walsh f)).Adj u v := by
  classical
  by_contra edge
  have h0 := (source_matching_consistency group span representatives f prime.1 (by norm_num) safe.canonical).constant_ne_zero
  let c : ℂ := (walsh f (fun _=>false))⁻¹
  have hc : c≠0 := inv_ne_zero h0
  let g := c • f
  have gs : Deck G g := safe.smul c
  have gp : Prime (⟨6,g⟩ : AnySignature ℂ) :=
    Holant.LocalDrafts.Hardness.FrozenFactorNormalization.prime_scaled (Units.mk0 c hc) prime
  have g0 : walsh g (fun _=>false)=1 := by
    rw [walsh_smul]
    exact inv_mul_cancel₀ h0
  have empty : weightGraph (walsh g)=⊥ := by
    ext u v
    simp only [SimpleGraph.bot_adj,iff_false]
    rintro ⟨huv,hn⟩
    apply edge
    refine ⟨u,v,huv,?_⟩
    rw [walsh_smul] at hn
    exact (mul_ne_zero_iff.mp hn).2
  have size := (Holant.ReedMuller.SupportReconstruction.source_reed_muller_support
    group span representatives g gp.1 (by norm_num) g0 gs.canonical empty).2.2.1
  norm_num at size

include group span prime safe in
theorem realizes (family : SignatureFamily ℂ)
    (hI : (⟨2,Holant.ReedMuller.WeightTwoIntegration.literalI⟩ : AnySignature ℂ)∈family)
    (mem : (⟨6,f⟩ : AnySignature ℂ)∈family) :
    Gadget.RealizesUpTo family .disequality Holant.ReedMuller.WeightTwoIntegration.even4 := by
  rcases Holant.ReedMuller.WeightTwoIntegration.source_native_factor_or_even4
    group span representatives family hI f prime.1 mem (by norm_num) safe.canonical
    (live_weight_graph G group span f prime safe) with factor|resource
  · exact False.elim (((PrimalityInterfaces.retained_complex_prime f).mp prime).2 factor)
  · exact resource.2


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicSixResource
end
