import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicEightTransfers

/-! A stable cyclic prime of arity at least eight forces the actual complete
group to have exactly two elements. Consequently the genuine larger cyclic
marking has no such minimum. Scalar descent stays in the original field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherExcluded
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureSourceRows
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
variable (phi : K→+*ℂ)
variable (cyclic : IsCyclic (completeGroup (RingHomRealization.mapFamily phi F)
  (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
variable (f : Signature K 8) (prime : Prime (⟨8,f⟩ : AnySignature K))
variable (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)

theorem c2_map (p : Bool) : (originalC2Binary p : Binary (K:=K)).map phi=
    (originalC2Binary p : Binary (K:=ℂ)) := by
  ext a b
  cases p <;> cases a <;> cases b <;>
    simp [originalC2Binary,X,Signature.disequality,Matrix.one_apply]

theorem c2_nonzero (p : Bool) : (originalC2Binary p : Binary (K:=K))≠0 := by
  cases p
  · intro zero
    have h:=congrFun₂ zero false false
    simpa [originalC2Binary] using h
  · intro zero
    have h:=congrFun₂ zero false true
    simpa [originalC2Binary,X,Signature.disequality] using h

include torsion hI cyclic prime stable in
theorem original_transfer_pure (T : Binary (K:=K)) (hT : T∈actualTransfers F) :
    ∃p : Bool,∃c : K,c≠0 ∧ T=c • originalC2Binary p := by
  obtain ⟨p,c,hc,he⟩ := GlobalCloseCompletionCyclicEightTransfers.current_transfer_pure
    F torsion hI phi cyclic f prime stable T hT
  have lifted : T.map phi=c • (originalC2Binary p : Binary (K:=K)).map phi := by
    rw [c2_map phi p]
    exact he
  obtain ⟨d,hd,form⟩ := scalar_descends phi (c2_nonzero (K:=K) p) hc lifted
  exact ⟨p,d,hd,form⟩

include torsion hI cyclic prime stable in
theorem key_cases (j : completeGroup F torsion) : j=1 ∨ j=markedKey F torsion hI := by
  rcases j with ⟨q,⟨U,hU,rfl⟩⟩
  obtain ⟨p,c,hc,he⟩ := original_transfer_pure F torsion hI phi cyclic f prime stable (U : Binary (K:=K)) hU
  cases p
  · left
    apply Subtype.ext
    apply pglToProjectiveClass_injective
    change projectiveClass (U : Binary (K:=K))=projectiveClass (1 : Binary (K:=K))
    rw [he,projectiveClass_smul _ hc]
    rfl
  · right
    apply Subtype.ext
    apply pglToProjectiveClass_injective
    change projectiveClass (U : Binary (K:=K))=pglToProjectiveClass (markedKey F torsion hI).val
    rw [markedKey_class,he,projectiveClass_smul _ hc]
    rfl

include torsion hI cyclic prime stable in
theorem card_two : Nat.card (completeGroup F torsion)=2 := by
  classical
  letI := completeGroup_finite F torsion
  letI := Fintype.ofFinite (completeGroup F torsion)
  have univ : (Finset.univ : Finset (completeGroup F torsion))={1,markedKey F torsion hI} := by
    ext j
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    exact key_cases F torsion hI phi cyclic f prime stable j
  have ne : (1 : completeGroup F torsion)≠markedKey F torsion hI := (markedKey_ne_one F torsion hI).symm
  rw [Nat.card_eq_fintype_card,←Finset.card_univ,univ]
  simp [ne]

omit f prime stable in
include torsion hI cyclic in
theorem no_higher {m : ℕ} (q : Signature K (m+2))
    (prime : Prime (⟨m+2,q⟩ : AnySignature K)) (higher : 8≤m+2)
    (stable : ∀g∈rawDeck F torsion q,MatchingOrZero (actualTransfers F) g)
    (notTwo : Nat.card (completeGroup F torsion)≠2) : False := by
  have size := (GlobalCloseCompletionCyclicHigherStructure.current_prime_reed_muller_support
    F torsion hI phi cyclic q prime higher stable).1
  have hm : m=6 := by omega
  subst m
  exact notTwo (card_two F torsion hI phi cyclic q prime stable)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherExcluded
end
