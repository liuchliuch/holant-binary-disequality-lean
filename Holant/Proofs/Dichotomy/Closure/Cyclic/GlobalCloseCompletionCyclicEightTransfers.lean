import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicKernelPure
import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicReedMuller

/-! An actual stable cyclic eight-port prime forces every original transfer
to be projectively I or X. This consumes the regenerated deck for the
original transfer, rather than postulating a C2 or normalized deck. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicEightTransfers
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CoefficientAtlas
namespace P
export GlobalCloseCompletionCyclicKernelPencil (pencil)
end P
namespace C
export GlobalCloseCompletionCyclicHigherField (actual_span matching_map)
export GlobalCloseCompletionCyclicHigherDeck (identity_map)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
variable (phi : K→+*ℂ)
variable (cyclic : IsCyclic (completeGroup (RingHomRealization.mapFamily phi F)
  (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
variable (f : Signature K 8) (prime : Prime (⟨8,f⟩ : AnySignature K))
variable (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)

include torsion hI cyclic prime stable in
theorem walsh_support : ∃e : Equiv.Perm (Fin 8),
    SupportRM (walsh (Tensor.reindex e.symm (RingHomRealization.mapSignature phi f))) := by
  obtain ⟨_,e,hsupport⟩ := GlobalCloseCompletionCyclicHigherStructure.current_prime_reed_muller_support
    F torsion hI phi cyclic f prime (by norm_num) stable
  refine ⟨e,?_⟩
  intro z
  rw [support_word_iff_code]
  have h:=hsupport (fun i=>boolEquiv (z (e.symm i)))
  have words : wordVector (fun i=>boolEquiv (z (e.symm i)))=(fun i=>z (e.symm i)) := by
    funext i
    exact boolEquiv.symm_apply_apply _
  rw [words] at h
  have coords : (fun p=>boolEquiv (z (e.symm (e p))))=vector z := by
    funext p
    rw [Equiv.symm_apply_apply]
    change boolEquiv (z p)=boolValue (z p)
    cases z p <;> rfl
  rw [coords] at h
  simpa only [GlobalCloseCompletionCyclicReedMuller.walsh_reindex,Tensor.reindex] using h

include torsion hI stable in
theorem ordered_matching (e : Equiv.Perm (Fin 8)) (T : Binary (K:=K))
    (hT : T∈actualTransfers F) :
    MatchingOrZero (actualTransfers (RingHomRealization.mapFamily phi F))
      (Signature.contract (T.map phi) (Tensor.reindex (ports 0).symm
        (Tensor.reindex e.symm (RingHomRealization.mapSignature phi f)))) := by
  let order : Equiv.Perm (Fin 8) := (ports 0).trans e
  have h:=DeckContraction.orderedClosure_matching F torsion hI f stable order T hT
  have hm:=C.matching_map phi F _ h
  convert hm using 1
  funext x
  simp only [Signature.contract,Tensor.reindex,RingHomRealization.mapSignature,
    _root_.map_sum,map_mul,Matrix.map_apply,order,Equiv.symm_trans_apply]

include torsion hI cyclic prime stable in
theorem current_transfer_pure (T : Binary (K:=K)) (hT : T∈actualTransfers F) :
    ∃p : Bool,∃c : ℂ,c≠0 ∧ T.map phi=c • (ClosureSourceRows.originalC2Binary p : Binary (K:=ℂ)) := by
  let H := RingHomRealization.mapFamily phi F
  let tau := ClosureFieldBridgeGroups.mappedTorsion phi F torsion
  let G := actualTransfers H
  have group : ProjectiveMatrixGroup G := actualTransfers_projectiveMatrixGroup H (actualTransfers_nonempty H) tau
  have span : ∀U∈G,∃a b : ℂ,U=P.pencil a b := C.actual_span H tau (C.identity_map phi hI) cyclic
  have member : T.map phi∈G := ClosureFieldBridgeGroups.actualTransfers_map phi hT
  obtain ⟨a,b,form⟩ := span _ member
  obtain ⟨e,support⟩ := walsh_support F torsion hI phi cyclic f prime stable
  let g := Tensor.reindex e.symm (RingHomRealization.mapSignature phi f)
  have idMember : (1 : Binary (K:=K))∈actualTransfers F :=
    (actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion).one_mem
  have identity : MatchingOrZero G (physicalCard g 0 false) := by
    have hi:=ordered_matching F torsion hI phi f stable e 1 idMember
    have mapped_identity : (1 : Binary (K:=K)).map phi=(Signature.equality : Kernel ℂ) := by
      ext u v
      cases u <;> cases v <;> simp [Matrix.one_apply,Signature.equality]
    rw [mapped_identity] at hi
    exact hi
  have weighted : MatchingOrZero G (Signature.contract (P.pencil a b) (Tensor.reindex (ports 0).symm g)) := by
    rw [←form]
    exact ordered_matching F torsion hI phi f stable e T hT
  have nonsingular : Matrix.det (P.pencil a b)≠0 := by rw [←form];exact group.det_ne_zero member
  have pure:=GlobalCloseCompletionCyclicKernelPure.kernel_pure G group span g support a b nonsingular identity weighted
  have nonzero : T.map phi≠0 := by
    intro zero
    have hd:=group.det_ne_zero member
    exact hd (by rw [zero];simp)
  rcases mul_eq_zero.mp pure with ha|hb
  · refine ⟨true,b,?_,?_⟩
    · intro zero
      apply nonzero
      rw [form]
      ext u v
      simp [P.pencil,ha,zero]
    · rw [form]
      ext u v
      simp [P.pencil,ha,ClosureSourceRows.originalC2Binary,X,Matrix.smul_apply,smul_eq_mul]
  · refine ⟨false,a,?_,?_⟩
    · intro zero
      apply nonzero
      rw [form]
      ext u v
      simp [P.pencil,hb,zero]
    · rw [form]
      ext u v
      simp [P.pencil,hb,ClosureSourceRows.originalC2Binary,Matrix.smul_apply,smul_eq_mul,
        Signature.equality,Matrix.one_apply]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicEightTransfers
end
