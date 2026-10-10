import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicHigherStructure
import Holant.ReedMuller.CoefficientAtlas.Source

/-! Full RM8 coefficients from an arbitrary cyclic I/X-span deck. The
original scalar and port translation/permutation are conclusions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicReedMuller
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CoefficientAtlas
open GlobalCloseCompletionCyclicHigherDeck GlobalCloseCompletionCyclicHigherStructure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable (G : Set (Binary (K:=ℂ))) (group : ProjectiveMatrixGroup G)
variable (span : ∀T∈G,∃a b : ℂ,T=fun u v=>a*Signature.equality u v+b*Signature.disequality u v)
private def atlasMatching (M : Holant.ReedMuller.FixedCoreDeck.WeightedMatching 6 3) :
    Holant.ReedMuller.CoefficientAtlas.WeightedMatching where
  ports := (Equiv.prodCongr (Equiv.refl (Fin 3)) finTwoEquiv).trans M.ports
  scalar := Units.mk0 M.constant M.constant_ne_zero
  ratio i := Units.mk0 (M.ratio i) (M.ratio_ne_zero i)

private theorem atlasMatching_value (M : Holant.ReedMuller.FixedCoreDeck.WeightedMatching 6 3) :
    (atlasMatching M).value = M.value := by
  funext w
  rw [M.value_eq_ratioProduct]
  rfl

include group span in
theorem safe_physical_deck (f : Signature ℂ 8) (safe : Deck G f) :
    Holant.ReedMuller.CoefficientAtlas.PhysicalDeck f := by
  intro p phase
  have hmatching := safe (Holant.ReedMuller.CoefficientAtlas.ports p) phase
  have card : Holant.ReedMuller.CoefficientAtlas.physicalCard f p phase =
      Signature.contract (Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows.originalC2Binary phase)
        (Tensor.reindex (Holant.ReedMuller.CoefficientAtlas.ports p).symm f) := by
    cases phase <;> rfl
  rw [card]
  rcases Holant.ReedMuller.FixedCoreDeck.walsh_matchingOrZero group span hmatching with
    zero | ⟨r,M,equation⟩
  · exact Or.inl zero
  · have size := Fintype.card_congr M.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at size
    have hr : r=3 := by omega
    subst r
    exact Or.inr ⟨atlasMatching M,(atlasMatching_value M).trans equation⟩

theorem walsh_reindex {n : ℕ} (f : Signature ℂ n) (e : Equiv.Perm (Fin n)) :
    walsh (Tensor.reindex e f)=Tensor.reindex e (walsh f) := by
  exact Holant.ReedMuller.CoefficientAtlas.coordinateAction_reindex walshInverse e f

include group span in
/-- The coordinate set is the fixed RM(1,3) evaluation code itself, under a
proved original-port permutation and actual bit translation. -/
theorem prime_exact_code (f : Signature ℂ 8)
    (prime : Prime (⟨8,f⟩ : AnySignature ℂ)) (safe : Deck G f) :
    ∃ e : Equiv.Perm (Fin 8), ∃ c : ℂ, ∃ a : BinaryVector 8, c≠0 ∧ ∀ x,
      f x = if (fun p => boolEquiv (x (e p)))+a∈code then c else 0 := by
  obtain ⟨_size,e,hsupport⟩ := prime_reed_muller_support G group span f prime (by norm_num) safe
  let g := Tensor.reindex e.symm f
  have gs : Deck G g := safe.reindex e.symm
  have support : SupportRM (walsh g) := by
    intro z
    rw [support_word_iff_code]
    have h := hsupport (fun i => boolEquiv (z (e.symm i)))
    have word : wordVector (fun i => boolEquiv (z (e.symm i))) = fun i => z (e.symm i) := by
      funext i
      exact boolEquiv.symm_apply_apply _
    rw [word] at h
    have coords : (fun p => boolEquiv (z (e.symm (e p)))) = vector z := by
      funext p
      rw [Equiv.symm_apply_apply]
      change boolEquiv (z p)=boolValue (z p)
      cases z p <;> rfl
    rw [coords] at h
    simpa only [g,walsh_reindex,Tensor.reindex] using h
  obtain ⟨c,a,_phase,equation,nonzero⟩ := source_rm_coefficient_atlas g support (safe_physical_deck G group span g gs)
  refine ⟨e,16*(c:ℂ),a,nonzero,?_⟩
  intro x
  have h := congrFun equation (fun p => x (e p))
  have coords : vector (fun p=>x (e p))=(fun p=>boolEquiv (x (e p))) := by
    funext p
    change boolValue (x (e p))=boolEquiv (x (e p))
    cases x (e p) <;> rfl
  rw [coords] at h
  simpa only [g,Tensor.reindex,Equiv.apply_symm_apply] using h


variable {K : Type*} [Field K] [NumberField K]
theorem current_prime_exact_code (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (phi : K→+*ℂ)
    (cyclic : IsCyclic (completeGroup (RingHomRealization.mapFamily phi F)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
    (f : Signature K 8) (prime : Prime (⟨8,f⟩ : AnySignature K))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    ∃e : Equiv.Perm (Fin 8),∃c : ℂ,∃a : BinaryVector 8,c≠0 ∧ ∀x,
      RingHomRealization.mapSignature phi f x=
        if (fun p=>boolEquiv (x (e p)))+a∈code then c else 0 :=
  prime_exact_code _
    (actualTransfers_projectiveMatrixGroup _ (actualTransfers_nonempty _)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion))
    (GlobalCloseCompletionCyclicHigherField.actual_span _ (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)
      (identity_map phi hI) cyclic) _ ((prime_mapSignature_iff phi _).mpr prime)
    (current_deck F torsion hI phi f stable)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicReedMuller
end
