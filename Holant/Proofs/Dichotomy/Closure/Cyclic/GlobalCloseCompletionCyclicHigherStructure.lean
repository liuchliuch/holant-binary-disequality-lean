import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicHigherDeck
import Holant.ReedMuller.WeightTwoIntegration.Structure
import Holant.ReedMuller.SupportReconstruction.Source
import Holant.Proofs.Algorithms.PrimalityInterfaces
import Holant.Proofs.Reductions.FrozenFactorNormalization.NormalizedTree

/-! The genuine I/X-span higher-prime theorem, including arbitrary cyclic
transfer weights. No literal C2-factor condition is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherStructure
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas
open GlobalCloseCompletionCyclicHigherDeck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable (G : Set (Binary (K:=ℂ))) (group : ProjectiveMatrixGroup G)
variable (span : ∀T∈G,∃a b : ℂ,T=fun u v=>a*Signature.equality u v+b*Signature.disequality u v)
include group span
theorem prime_weight_graph_empty {m : ℕ} (f : Signature ℂ (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature ℂ)) (higher : 8≤m+2) (safe : Deck G f) :
    weightGraph (walsh f)=⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj,iff_false]
  intro edge
  rcases Holant.ReedMuller.WeightTwoIntegration.source_weight_two_structure
    group span representatives f prime.1 (by omega) safe.canonical
    ⟨u,v,edge⟩ with factor | exceptional
  · exact ((PrimalityInterfaces.retained_complex_prime f).mp prime).2 factor
  · have he := exceptional.arity
    omega

/-- The normalization scalar is recovered from the original tensor's own
nonzero Walsh origin. Support is then transported back exactly. -/
theorem prime_reed_muller_support {m : ℕ} (f : Signature ℂ (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature ℂ)) (higher : 8≤m+2) (safe : Deck G f) :
    m+2=8 ∧ ∃ e : Holant.ReedMuller.CoefficientAtlas.Point ≃ Fin (m+2),
      ∀ x : Holant.ReedMuller.LowArity.BinaryVector (m+2),
        walsh f (Holant.ReedMuller.FlatNetwork.wordVector x)≠0 ↔
          (fun p => x (e p))∈Holant.ReedMuller.CoefficientAtlas.code := by
  have h0 := (source_matching_consistency group span representatives f prime.1 (by omega) safe.canonical).constant_ne_zero
  let c : ℂ := (walsh f (fun _ => false))⁻¹
  have hc : c≠0 := inv_ne_zero h0
  let g := c • f
  have gs : Deck G g := safe.smul c
  have gp : Prime (⟨m+2,g⟩ : AnySignature ℂ) :=
    Holant.LocalDrafts.Hardness.FrozenFactorNormalization.prime_scaled (Units.mk0 c hc) prime
  have g0 : walsh g (fun _ => false)=1 := by
    rw [walsh_smul]
    exact inv_mul_cancel₀ h0
  obtain ⟨_slices,_code,size,e,he⟩ :=
    Holant.ReedMuller.SupportReconstruction.source_reed_muller_support
      group span representatives g gp.1 (by omega) g0 gs.canonical
      (prime_weight_graph_empty G group span g gp higher gs)
  refine ⟨size,e,?_⟩
  intro x
  have hh := he x
  rw [walsh_smul] at hh
  change (c * walsh f (Holant.ReedMuller.FlatNetwork.wordVector x)≠0 ↔
    (fun p=>x (e p))∈Holant.ReedMuller.CoefficientAtlas.code) at hh
  exact ⟨fun live=>hh.mp (mul_ne_zero hc live),
    fun live=>(mul_ne_zero_iff.mp (hh.mpr live)).2⟩


variable {K : Type*} [Field K] [NumberField K]
omit group span in
theorem current_prime_reed_muller_support (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (phi : K→+*ℂ)
    (cyclic : IsCyclic (completeGroup (RingHomRealization.mapFamily phi F)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
    {m : ℕ} (f : Signature K (m+2)) (prime : Prime (⟨m+2,f⟩ : AnySignature K))
    (higher : 8≤m+2) (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    m+2=8 ∧ ∃ e : Holant.ReedMuller.CoefficientAtlas.Point ≃ Fin (m+2),
      ∀x : Holant.ReedMuller.LowArity.BinaryVector (m+2),
        walsh (RingHomRealization.mapSignature phi f) (Holant.ReedMuller.FlatNetwork.wordVector x)≠0 ↔
          (fun p=>x (e p))∈Holant.ReedMuller.CoefficientAtlas.code :=
  prime_reed_muller_support _
    (actualTransfers_projectiveMatrixGroup _ (actualTransfers_nonempty _)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion))
    (GlobalCloseCompletionCyclicHigherField.actual_span _ (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)
      (identity_map phi hI) cyclic) _ ((prime_mapSignature_iff phi _).mpr prime) higher
    (current_deck F torsion hI phi f stable)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherStructure
end
