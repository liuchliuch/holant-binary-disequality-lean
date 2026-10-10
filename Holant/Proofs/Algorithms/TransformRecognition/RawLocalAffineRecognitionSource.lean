import Holant.Proofs.Algorithms.TransformRecognition.RawAffineRecognitionSource
import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineBodySource
import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineRecognitionMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineBranchMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineRecognitionSource
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalLocalAffineSystem
variable {s : ℕ} (arity : Fin s → ℕ)

noncomputable def branches (input : OriginalFamilyInput.Input arity) : List (List (Sparse.Poly (Width arity) 1)) :=
  (RawLocalAffineCandidateSource.generated arity input).attach.map
    (fun c => body arity (RawLocalAffineCandidateSource.normalizedFamily arity input c.val c.property))
noncomputable def combined (input : OriginalFamilyInput.Input arity) : List (Sparse.Poly (Width arity) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra arity) :: FiniteSystemDisjunction.combine (branches arity input)

theorem branchSystems_wire (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    RawLocalAffineRecognitionMachine.systems (OriginalFamilyPackingSource.fromSource arity input disequality) =
      (branches arity input).map RationalInputMachine.bodyWire := by
  unfold RawLocalAffineRecognitionMachine.systems branches
  rw [List.map_map]
  have h : (RawLocalAffineCandidateSource.generated arity input).attach.map
      (fun c => RawLocalAffineBranchMachine.body
        (OriginalFamilyPackingSource.fromSource arity input disequality,c.val)) =
      (RawLocalAffineCandidateSource.generated arity input).attach.map
        (fun c => RationalInputMachine.bodyWire (body arity
          (RawLocalAffineCandidateSource.normalizedFamily arity input c.val c.property))) := by
    apply List.map_congr_left
    intro c _
    exact RawLocalAffineBodySource.normalized_body arity input disequality c.val c.property
  rw [List.attach_map_val (l := RawLocalAffineCandidateSource.generated arity input)
    (f := fun t : RawLocalAffineFamilyEnumeration.Candidate => RawLocalAffineBranchMachine.body (OriginalFamilyPackingSource.fromSource arity input disequality,t))] at h
  simpa only [RawLocalAffineCandidateSource.generated,LocalAffineAllocationSource.family_exact,Function.comp_def] using h

theorem body_wire (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    RawLocalAffineRecognitionMachine.body (OriginalFamilyPackingSource.fromSource arity input disequality) =
      RationalInputMachine.bodyWire (combined arity input) := by
  rw [RawLocalAffineRecognitionMachine.body,RawLocalAffineRecognitionMachine.allocated,LocalAffineAllocationSource.width_source,
    branchSystems_wire,RationalDisjunctionMachine.combine_wire,RationalMatrixMachine.guard_wire]
  rfl

theorem canonical_body (input : OriginalFamilyInput.Input arity) (B : LocalAffineBranch.Branch arity) :
    ∃ S ∈ branches arity input, S=body arity B := by
  let c := RawLocalAffineCandidateSource.sourceFamily arity B
  have hc : c ∈ RawLocalAffineCandidateSource.generated arity input :=
    RawLocalAffineCandidateSource.sourceFamily_mem arity input B
  refine ⟨body arity (RawLocalAffineCandidateSource.normalizedFamily arity input c hc),
    List.mem_map.mpr ⟨⟨c,hc⟩,List.mem_attach _ _,rfl⟩,?_⟩
  apply RawAffineRecognitionSource.bodyWire_injective
  exact (RawLocalAffineBodySource.normalized_body arity input true c hc).symm.trans
    (RawLocalAffineBodySource.canonical_body arity input true B)

theorem combined_zero_iff (input : OriginalFamilyInput.Input arity) (z : Fin (Width arity) → ℂ) :
    (∀ p ∈ combined arity input, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      ∃ B : LocalAffineBranch.Branch arity,
        ∀ p ∈ body arity B, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  rw [combined,List.forall_mem_cons,FiniteSystemDisjunction.combine_zero_iff]
  constructor
  · rintro ⟨_,S,hS,hz⟩
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hS
    exact ⟨RawLocalAffineCandidateSource.normalizedFamily arity input c.val c.property,hz⟩
  · rintro ⟨B,hB⟩
    obtain ⟨S,hS,rfl⟩ := canonical_body arity input B
    exact ⟨hB _ (List.mem_cons_self ..),_,hS,hB⟩

theorem bound_solution_iff (input : OriginalFamilyInput.Input arity)
    (w : Fin (Entries arity) → AlgebraicComplex) :
    (∃ z : Fin (Width arity) → ℂ, Bound arity w z ∧
      ∀ p ∈ combined arity input, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      LocalAffineBranch.Shared (OriginalAffineSystem.sourceVertex arity w) (OriginalAffineSystem.sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) := by
  constructor
  · rintro ⟨z,hb,hz⟩
    obtain ⟨B,hB⟩ := (combined_zero_iff arity input z).mp hz
    obtain ⟨he,hn⟩ := constraints_of_zero arity w z hb B hB
    exact LocalAffineBranch.shared_of_solution _ _ _ B (point arity z) he hn
  · intro h
    obtain ⟨B,y,he,hn⟩ := LocalAffineBranch.solution_of_shared _ _ _ h
    exact ⟨fill arity w y,fill_bound arity w y,
      (combined_zero_iff arity input _).mpr ⟨B,zero_of_constraints arity w y B he hn⟩⟩

theorem request_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    RawLocalAffineRecognitionMachine.request (OriginalFamilyPackingSource.fromSource arity input disequality) =
      RationalInputMachine.fromSource (OriginalVariableLayout.descriptors
        (OriginalFamilyInput.pack arity input disequality)) (combined arity input)
        (OriginalVariableLayout.binding (Entries arity) (Count arity)) := by
  simp only [RawLocalAffineRecognitionMachine.request,RawLocalAffineRecognitionMachine.allocated,LocalAffineAllocationSource.width_source,
    LocalAffineAllocationSource.count_raw,OriginalAllocatedPackingMachine.width_source,
    OriginalFamilyPackingSource.roots_exact,OriginalAllocatedPackingMachine.addresses_source,body_wire,
    RationalInputMachine.fromSource]

noncomputable def answer (input : OriginalFamilyInput.Input arity)
    (hv : OriginalFamilyInput.Valid arity input) (disequality : Bool) : Bool :=
  OriginalSystemDecision.answer (OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input disequality))
    (OriginalAffineBranchMachine.descriptors_valid arity _ (OriginalFamilyInput.pack_valid arity input hv disequality))
    (combined arity input) (OriginalVariableLayout.binding (Entries arity) (Count arity))

theorem source_outputs (input : OriginalFamilyInput.Input arity)
    (hv : OriginalFamilyInput.Valid arity input) (disequality : Bool) :
    ∃ bound, Nonempty (TM2OutputsInTime RawLocalAffineRecognitionMachine.machine.computer
      (RawLocalAffineRecognitionMachine.encoding.encode (OriginalFamilyPackingSource.fromSource arity input disequality))
      (some (encodingBoolBool.encode (answer arity input hv disequality))) bound) := by
  obtain ⟨bound,⟨run⟩⟩ := OriginalSystemMachine.source_outputs
    (OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input disequality))
    (OriginalAffineBranchMachine.descriptors_valid arity _ (OriginalFamilyInput.pack_valid arity input hv disequality))
    (combined arity input) (OriginalVariableLayout.binding (Entries arity) (Count arity))
  have prepared := RawLocalAffineRecognitionMachine.prepare.outputs (OriginalFamilyPackingSource.fromSource arity input disequality)
  rw [request_exact] at prepared
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ prepared run⟩⟩

theorem answer_correct (input : OriginalFamilyInput.Input arity)
    (hv : OriginalFamilyInput.Valid arity input) (disequality : Bool)
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (hG : ∀ i x, (input i x).Represents (G i x : ℂ)) :
    answer arity input hv disequality=true ↔
      LocalAffineBranch.Shared G (OriginalFamilyInput.edge disequality) (algebraMap AlgebraicComplex ℂ) := by
  let w := OriginalFamilyInput.values arity G disequality
  have hw := OriginalFamilyInput.pack_represents arity input G hG disequality
  have hd : ∀ i, (OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input disequality) i).Represents
      (OriginalAffineDecision.originalValues arity w i : ℂ) := by
    intro i
    rw [congrFun (OriginalAffineDecision.originalValues_coe arity w) i]
    exact OriginalVariableLayout.descriptors_represents _ _ hw i
  rw [answer,OriginalSystemDecision.answer_correct _ _ _ hd (combined arity input) _ (by exact List.mem_cons_self ..)]
  simp only [OriginalAffineDecision.originalValues_coe]
  simp_rw [RationalInputSystem.system_zero_iff]
  simpa only [w,OriginalTensorRows.Bound,OriginalLocalAffineSystem.Bound,OriginalFamilyInput.sourceVertex_values,OriginalFamilyInput.sourceEdge_values] using
    bound_solution_iff arity input w

end Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineRecognitionSource
