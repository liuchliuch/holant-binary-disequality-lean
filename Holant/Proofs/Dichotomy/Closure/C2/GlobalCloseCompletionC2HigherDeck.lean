import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SafeSymmetry
import Holant.ReedMuller.MatchingConsistency.Source

/-! The actual original-field order-two deck supplies literal fixed I/X
representatives in the original port order. The existing Walsh matching
coherence theorem therefore applies with no native-M phase hypothesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2HigherDeck
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas
open GlobalCloseCompletionC2TensorMatching GlobalCloseCompletionC2SafeSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

/-- An analytic matrix set used only to state the exact matching theorem. -/
def ixGroup : Set (Binary (K := ℂ)) :=
  {B | ∃ p : Bool, ∃ c : ℂ, c ≠ 0 ∧ B = c • originalC2Binary p}

theorem binary_mul (p q : Bool) :
    originalC2Binary (L := ℂ) p * originalC2Binary q = originalC2Binary (p ^^ q) := by
  cases p <;> cases q <;> simp [originalC2Binary,X_mul_X]

theorem ixGroup_group : ProjectiveMatrixGroup ixGroup where
  one_mem := ⟨false,1,one_ne_zero,by simp [originalC2Binary]⟩
  mul_mem := by
    rintro U ⟨p,c,hc,rfl⟩ V ⟨q,d,hd,rfl⟩
    exact ⟨p ^^ q,c*d,mul_ne_zero hc hd,by rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,binary_mul]⟩
  inverse_mem := by
    rintro U ⟨p,c,hc,rfl⟩
    refine ⟨c⁻¹ • originalC2Binary p,⟨p,c⁻¹,inv_ne_zero hc,rfl⟩,?_,?_⟩
    · rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,binary_mul,Bool.xor_self]
      simp [hc,originalC2Binary]
    · rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,binary_mul,Bool.xor_self]
      simp [hc,originalC2Binary]
  scalar_mem := by
    rintro U ⟨p,c,hc,rfl⟩ d hd
    exact ⟨p,d*c,mul_ne_zero hd hc,by rw [smul_smul]⟩

theorem ixGroup_span (B : Binary (K := ℂ)) (h : B ∈ ixGroup) :
    ∃ a b : ℂ, B = fun u v => a*Signature.equality u v+b*Signature.disequality u v := by
  obtain ⟨p,c,_hc,rfl⟩ := h
  cases p
  · refine ⟨c,0,?_⟩
    ext u v
    simp [originalC2Binary,Signature.equality,Matrix.one_apply]
  · refine ⟨0,c,?_⟩
    ext u v
    simp [originalC2Binary,X]

def representatives : FixedIXRepresentatives where
  kernel p := originalC2Binary p
  scale _ := 1
  scale_ne_zero _ := one_ne_zero
  exact := by
    intro p
    cases p <;> ext a b <;> simp [originalC2Binary,X,Signature.equality,Matrix.one_apply]

theorem literal_matching {I : Type*} (f : Tensor ℂ I) (h : LiteralMatching f) :
    MatchingOrZero ixGroup f := by
  rcases h with rfl | ⟨k,ports,label,c,hc,rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨⟨k,ports,fun i => originalC2Binary (label i),c⟩,?_,hc,rfl⟩
    intro i
    change SafeBinary ixGroup (originalC2Binary (label i))
    refine ⟨!(label i),1,one_ne_zero,?_⟩
    cases h : label i <;> simp [h,transfer,originalC2Binary,X_mul_X]

theorem safe_deck {m : ℕ} (f : Signature ℂ (m+2)) (safe : Safe f) :
    CanonicalMatchingDeck ixGroup representatives f := by
  intro i j _hij p
  exact literal_matching _ (safe (Holant.Dihedral.CompatibleClosure.pairOrder i j) p)

theorem safe_consistent {m : ℕ} (f : Signature ℂ (m+2)) (nonzero : f ≠ 0)
    (higher : 6 ≤ m+2) (safe : Safe f) : Consistent (walsh f) :=
  source_matching_consistency ixGroup_group ixGroup_span representatives f nonzero higher
    (safe_deck f safe)

variable {K : Type*} [Field K] [NumberField K]

theorem current_consistent (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
    (phi : K →+* ℂ) {m : ℕ} (f : Signature K (m+2)) (nonzero : f≠0)
    (higher : 6≤m+2)
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g) :
    Consistent (walsh (RingHomRealization.mapSignature phi f)) := by
  apply safe_consistent _ _ higher ((current_safe F torsion hI cardTwo f stable).map phi)
  intro zero
  apply nonzero
  funext x
  apply phi.injective
  simpa only [RingHomRealization.mapSignature,Pi.zero_apply,map_zero] using congrFun zero x

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2HigherDeck
end
