import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2HigherDeck
import Holant.ReedMuller.WeightTwoIntegration.Structure
import Holant.ReedMuller.SupportReconstruction.Source
import Holant.Proofs.Algorithms.PrimalityInterfaces
import Holant.Proofs.Reductions.FrozenFactorNormalization.NormalizedTree

/-! Actual C2 higher-prime reconstruction. Matching agreement comes from the
literal deck. A higher prime has empty Walsh weight-two graph and necessarily
has eight ports with the Reed--Muller support. The RM8 case is retained as a
real mathematical alternative; it is not incorrectly forced to factor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2HigherStructure
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas
open GlobalCloseCompletionC2TensorMatching GlobalCloseCompletionC2SafeSymmetry
open GlobalCloseCompletionC2HigherDeck
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem literal_smul {I : Type*} (f : Tensor ℂ I) (h : LiteralMatching f) (c : ℂ) :
    LiteralMatching (c • f) := by
  by_cases hc : c=0
  · left
    simp [hc]
  rcases h with rfl | ⟨k,ports,label,d,hd,rfl⟩
  · exact Or.inl (smul_zero c)
  · refine Or.inr ⟨k,ports,label,c*d,mul_ne_zero hc hd,?_⟩
    funext w
    simp only [Pi.smul_apply,smul_eq_mul,productValue,mul_assoc]

theorem safe_smul {m : ℕ} (f : Signature ℂ (m+2)) (safe : Safe f) (c : ℂ) :
    Safe (c • f) := by
  intro e p
  have he : Tensor.reindex e.symm (c • f)=c • Tensor.reindex e.symm f := rfl
  rw [he]
  have hcontract : Signature.contract (Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows.originalC2Binary p)
      (c • Tensor.reindex e.symm f)=c • Signature.contract
        (Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows.originalC2Binary p)
        (Tensor.reindex e.symm f) := by
    funext w
    simp only [Signature.contract,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
    ring
  rw [hcontract]
  exact literal_smul _ (safe e p) c

theorem prime_weight_graph_empty {m : ℕ} (f : Signature ℂ (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature ℂ)) (higher : 8≤m+2) (safe : Safe f) :
    weightGraph (walsh f)=⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj,iff_false]
  intro edge
  rcases Holant.ReedMuller.WeightTwoIntegration.source_weight_two_structure
    ixGroup_group ixGroup_span representatives f prime.1 (by omega) (safe_deck f safe)
    ⟨u,v,edge⟩ with factor | exceptional
  · exact ((PrimalityInterfaces.retained_complex_prime f).mp prime).2 factor
  · have he := exceptional.arity
    omega

/-- The normalization scalar is recovered from the original tensor's own
nonzero Walsh origin. Support is then transported back exactly. -/
theorem prime_reed_muller_support {m : ℕ} (f : Signature ℂ (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature ℂ)) (higher : 8≤m+2) (safe : Safe f) :
    m+2=8 ∧ ∃ e : Holant.ReedMuller.CoefficientAtlas.Point ≃ Fin (m+2),
      ∀ x : Holant.ReedMuller.LowArity.BinaryVector (m+2),
        walsh f (Holant.ReedMuller.FlatNetwork.wordVector x)≠0 ↔
          (fun p => x (e p))∈Holant.ReedMuller.CoefficientAtlas.code := by
  have h0 := (safe_consistent f prime.1 (by omega) safe).constant_ne_zero
  let c : ℂ := (walsh f (fun _ => false))⁻¹
  have hc : c≠0 := inv_ne_zero h0
  let g := c • f
  have gs : Safe g := safe_smul f safe c
  have gp : Prime (⟨m+2,g⟩ : AnySignature ℂ) :=
    Holant.LocalDrafts.Hardness.FrozenFactorNormalization.prime_scaled (Units.mk0 c hc) prime
  have g0 : walsh g (fun _ => false)=1 := by
    rw [walsh_smul]
    exact inv_mul_cancel₀ h0
  obtain ⟨_slices,_code,size,e,he⟩ :=
    Holant.ReedMuller.SupportReconstruction.source_reed_muller_support
      ixGroup_group ixGroup_span representatives g gp.1 (by omega) g0 (safe_deck g gs)
      (prime_weight_graph_empty g gp higher gs)
  refine ⟨size,e,?_⟩
  intro x
  have hh := he x
  rw [walsh_smul] at hh
  simp only [Pi.smul_apply,smul_eq_mul,mul_ne_zero_iff] at hh
  exact ⟨fun h=>hh.mp ⟨hc,h⟩,fun h=>(hh.mpr h).2⟩

variable {K : Type*} [Field K] [NumberField K]

theorem current_prime_reed_muller_support (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
    (phi : K →+* ℂ) {m : ℕ} (f : Signature K (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature K)) (higher : 8≤m+2)
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    m+2=8 ∧ ∃ e : Holant.ReedMuller.CoefficientAtlas.Point ≃ Fin (m+2),
      ∀ x : Holant.ReedMuller.LowArity.BinaryVector (m+2),
        walsh (RingHomRealization.mapSignature phi f) (Holant.ReedMuller.FlatNetwork.wordVector x)≠0 ↔
          (fun p => x (e p))∈Holant.ReedMuller.CoefficientAtlas.code :=
  prime_reed_muller_support _ ((prime_mapSignature_iff phi _).mpr prime) higher
    ((current_safe F torsion hI cardTwo f stable).map phi)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2HigherStructure
end
