import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicMatchingCone
import Holant.Platonic.RainbowLocalization.PhysicalKernelLift

/-! All-arity literal current cards and actual kernel lifts for T/O/I.
Every complex test retains an original-field actual representative and its
nonzero normalization scalar. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicHigherCards
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.Platonic.RainbowLocalization.Physical
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open scoped BigOperators

def directions (g : PlatonicModel) : Set (Matrix Bool Bool ℂ) := {U | groupDirection g U}

theorem directions_group (g : PlatonicModel) : ProjectiveMatrixGroup (directions g) :=
  Holant.Projective.FiniteGroupFacts.model_projectiveMatrixGroup g

theorem directions_safe_iff (g : PlatonicModel) (U : Matrix Bool Bool ℂ) :
    SafeBinary (directions g) U ↔ groupDirection g U := by
  have he : U*(MatchingContractionClosure.X : Matrix Bool Bool ℂ)=
      multiply U MatchingProductBridge.X := by
    ext a b
    cases b <;> simp [Matrix.mul_apply,multiply,Fintype.sum_bool,MatchingContractionClosure.X,
      MatchingProductBridge.X,Signature.disequality,add_comm]
  change groupDirection g (U*MatchingContractionClosure.X) ↔ groupDirection g U
  rw [he]
  exact groupDirection_right_X_iff g U

theorem directions_X (g : PlatonicModel) :
    (MatchingContractionClosure.X : Matrix Bool Bool ℂ)∈directions g :=
  GlobalCloseCompletionPlatonicCards.x_direction g

theorem directions_reversal (g : PlatonicModel) : ReversalStable (directions g) := by
  intro U hU
  exact Holant.Certificates.RainbowOrbit.groupDirection_mul g
    (Holant.Certificates.RainbowOrbit.groupDirection_mul g (directions_X g)
      (groupDirection_transpose g hU)) (directions_X g)

theorem matching_scale {P : Type*} (G : Set (Matrix Bool Bool ℂ))
    (q : Tensor ℂ P) (hq : MatchingOrZero G q) (c : ℂ) : MatchingOrZero G (c • q) := by
  by_cases hc : c=0
  · exact Or.inl (by simp [hc])
  rcases hq with rfl | ⟨M,hM,hs,rfl⟩
  · exact Or.inl (smul_zero _)
  · let N : Presentation ℂ P := {M with scalar := c*M.scalar}
    refine Or.inr ⟨N,hM,mul_ne_zero hc hs,?_⟩
    funext x
    simp only [Presentation.tensor,productValue,N,Pi.smul_apply,smul_eq_mul,mul_assoc]

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (g : PlatonicModel)
variable (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL g)

include literal in
theorem complex_matching {m : ℕ} (q : Signature L m)
    (hq : MatchingOrZero (actualTransfers F) q) :
    MatchingOrZero (directions g) (RingHomRealization.mapSignature (complexEmbedding phi) q) := by
  rcases hq with rfl | ⟨M,hM,hs,rfl⟩
  · left
    funext x
    exact map_zero _
  · let N : Presentation ℂ (Fin m) :=
      ⟨M.edges,M.ports,fun e => (M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
    refine Or.inr ⟨N,?_,(map_ne_zero _).mpr hs,?_⟩
    · intro e
      apply (directions_safe_iff g _).mpr
      exact GlobalCloseCompletionPlatonicMatchingCone.safe_direction phi F torsion g literal _ (hM e)
    · ext x
      simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]

include literal in
theorem ordered_card {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : Equiv.Perm (Fin (m+2))) (K : Matrix Bool Bool ℂ) (hk : groupDirection g K) :
    MatchingOrZero (directions g) (Signature.contract K
      (Tensor.reindex p (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
  obtain ⟨j,c,hc,he⟩ := GlobalCloseCompletionPlatonicCards.kernel_alignment phi F torsion g literal K hk
  let B := actualRepresentative F torsion j
  let key : RawCardKey m (completeGroup F torsion) := (fun _ => none,p.symm,j,false)
  have hraw : rawCard F torsion f key=
      Signature.contract (nativePair B) (Tensor.reindex p f) := by
    simp only [rawCard,key,orientBinary,Bool.false_eq_true,ite_false,ClosureSourceRows.dress_none]
    rfl
  have hpair : nativePair (B.map (complexEmbedding phi))=c • K := by
    rw [he]
    ext a b
    rw [nativePair_apply]
    change c*nativePair K (!a) (!b)=c*K a b
    rw [nativePair_apply,Bool.not_not,Bool.not_not]
  have hkernel (a b : Bool) : complexEmbedding phi (nativePair B a b)=c*K a b := by
    rw [nativePair_apply]
    have hh := congrFun (congrFun hpair a) b
    rw [nativePair_apply] at hh
    exact hh
  have mapped : RingHomRealization.mapSignature (complexEmbedding phi) (rawCard F torsion f key)=
      c • Signature.contract K (Tensor.reindex p
        (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
    rw [hraw]
    ext x
    simp only [RingHomRealization.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
      hkernel,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  have h := complex_matching phi F torsion g literal _ (stable _ (Or.inr ⟨key,rfl⟩))
  rw [mapped] at h
  have hu := matching_scale _ _ h c⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hu

include literal in
noncomputable def actualKernelLift : ActualKernelLift (mapFamily (complexEmbedding phi) F) (directions g) := by
  classical
  have h (K : directions g) : ∃ j : completeGroup F torsion, ∃ c : ℂ, c≠0 ∧
      (actualRepresentative F torsion j).map (complexEmbedding phi)=c • nativePair K.val :=
    GlobalCloseCompletionPlatonicCards.kernel_alignment phi F torsion g literal K.val K.property
  choose j c hc he using h
  exact {
    binary := fun K => (actualRepresentative F torsion (j K)).map (complexEmbedding phi)
    scalar := c
    scalar_ne_zero := hc
    normalization := he
    actual := fun K => (ClosureFieldBridgeGroups.actual_map (complexEmbedding phi)
      (actualRepresentative_actual F torsion (j K))).1 }


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicHigherCards
end
