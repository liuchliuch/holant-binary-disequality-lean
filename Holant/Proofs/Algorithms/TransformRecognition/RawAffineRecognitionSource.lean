import Holant.Proofs.Algorithms.TransformRecognition.RawAffineBodyNormalization
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineDisjunction


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineRecognitionSource
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalAffineSystem
variable {s : ℕ} (arity : Fin s → ℕ)

/-- The rational wire representation loses no sparse term, order or
multiplicity, including explicit zero terms. -/
theorem termWire_injective {n : ℕ} : Function.Injective (RationalInputMachine.termWire (n:=n)) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ h
  apply Prod.ext
  · exact List.ofFn_injective (congrArg Prod.fst h)
  · funext i
    have hi : i=0 := Fin.eq_zero i
    subst i
    exact congrArg Prod.snd h

theorem rowWire_injective {n : ℕ} : Function.Injective (RationalInputMachine.rowWire (n:=n)) :=
  List.map_injective_iff.mpr termWire_injective

theorem bodyWire_injective {n : ℕ} : Function.Injective (RationalInputMachine.bodyWire (n:=n)) :=
  List.map_injective_iff.mpr rowWire_injective

noncomputable def branches (input : OriginalFamilyInput.Input arity) : List (List (Sparse.Poly (Width arity) 1)) :=
  (RawAffineCandidateSource.generated arity input).attach.map
    (fun c => body arity (RawAffineCandidateSource.normalized arity input c.val c.property))
noncomputable def combined (input : OriginalFamilyInput.Input arity) : List (Sparse.Poly (Width arity) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra arity) :: FiniteSystemDisjunction.combine (branches arity input)

theorem branchSystems_wire (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    RawAffineRecognitionMachine.branchSystems (OriginalFamilyPackingSource.fromSource arity input disequality) =
      (branches arity input).map RationalInputMachine.bodyWire := by
  unfold RawAffineRecognitionMachine.branchSystems branches
  rw [List.map_map]
  have h : (RawAffineCandidateSource.generated arity input).attach.map
      (fun c => RationalAffineBodyMachine.body (RawAffineBranchMachine.bodyInput
        (OriginalFamilyPackingSource.fromSource arity input disequality,c.val))) =
      (RawAffineCandidateSource.generated arity input).attach.map
        (fun c => RationalInputMachine.bodyWire (body arity
          (RawAffineCandidateSource.normalized arity input c.val c.property))) := by
    apply List.map_congr_left
    intro c _
    exact RawAffineBodyNormalization.body_exact arity input disequality c.val c.property
  rw [List.attach_map_val (l := RawAffineCandidateSource.generated arity input)
    (f := fun t : RawAffineBranchMachine.Templates => RationalAffineBodyMachine.body
      (RawAffineBranchMachine.bodyInput (OriginalFamilyPackingSource.fromSource arity input disequality,t)))] at h
  simpa only [RawAffineCandidateSource.generated,RawAffineBranchSource.family_exact,Function.comp_def] using h

theorem body_wire (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    RawAffineRecognitionMachine.body (OriginalFamilyPackingSource.fromSource arity input disequality) =
      RationalInputMachine.bodyWire (combined arity input) := by
  rw [RawAffineRecognitionMachine.body,OriginalFamilyPackingSource.width_exact,
    branchSystems_wire,RationalDisjunctionMachine.combine_wire,RationalMatrixMachine.guard_wire]
  rfl

theorem canonical_body (input : OriginalFamilyInput.Input arity) (B : AffineBranch.Branch arity) :
    ∃ S ∈ branches arity input, S=body arity B := by
  let c := (RawAffineBranchSource.fromSource arity input true B).2
  have hc : c ∈ RawAffineCandidateSource.generated arity input := RawAffineFamilyEnumeration.source_mem arity input B
  refine ⟨body arity (RawAffineCandidateSource.normalized arity input c hc),
    List.mem_map.mpr ⟨⟨c,hc⟩,List.mem_attach _ _,rfl⟩,?_⟩
  apply bodyWire_injective
  have h := RawAffineBodyNormalization.body_exact arity input true c hc
  have hraw := RawAffineBranchSource.body_exact arity input true B
  change RationalAffineBodyMachine.body
    (RawAffineBranchMachine.bodyInput (RawAffineBranchSource.fromSource arity input true B)) = _ at h
  rw [hraw,OriginalAffineBodySource.body_exact] at h
  exact h.symm

theorem combined_zero_iff (input : OriginalFamilyInput.Input arity) (z : Fin (Width arity) → ℂ) :
    (∀ p ∈ combined arity input, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      ∃ B : AffineBranch.Branch arity,
        ∀ p ∈ body arity B, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  rw [combined,List.forall_mem_cons,FiniteSystemDisjunction.combine_zero_iff]
  constructor
  · rintro ⟨_,S,hS,hz⟩
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hS
    exact ⟨RawAffineCandidateSource.normalized arity input c.val c.property,hz⟩
  · rintro ⟨B,hB⟩
    obtain ⟨S,hS,rfl⟩ := canonical_body arity input B
    exact ⟨hB _ (List.mem_cons_self ..),_,hS,hB⟩

theorem bound_solution_iff (input : OriginalFamilyInput.Input arity)
    (w : Fin (Entries arity) → AlgebraicComplex) :
    (∃ z : Fin (Width arity) → ℂ, Bound arity w z ∧
      ∀ p ∈ combined arity input, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      AffineBranch.Shared (sourceVertex arity w) (sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) := by
  have h : ∀ z : Fin (Width arity) → ℂ,
      (∀ p ∈ combined arity input, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
      ∀ p ∈ OriginalAffineDisjunction.combined arity,
        SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 :=
    fun z => (combined_zero_iff arity input z).trans (OriginalAffineDisjunction.combined_zero_iff arity z).symm
  simp_rw [h]
  exact OriginalAffineDisjunction.bound_solution_iff arity w

theorem request_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    RawAffineRecognitionMachine.request (OriginalFamilyPackingSource.fromSource arity input disequality) =
      RationalInputMachine.fromSource (OriginalVariableLayout.descriptors
        (OriginalFamilyInput.pack arity input disequality)) (combined arity input)
        (OriginalVariableLayout.binding (Entries arity) (s+1)) := by
  simp only [RawAffineRecognitionMachine.request,OriginalFamilyPackingSource.width_exact,
    OriginalFamilyPackingSource.roots_exact,OriginalFamilyPackingSource.addresses_exact,body_wire,
    RationalInputMachine.fromSource]

noncomputable def answer (input : OriginalFamilyInput.Input arity)
    (hv : OriginalFamilyInput.Valid arity input) (disequality : Bool) : Bool :=
  OriginalSystemDecision.answer (OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input disequality))
    (OriginalAffineBranchMachine.descriptors_valid arity _ (OriginalFamilyInput.pack_valid arity input hv disequality))
    (combined arity input) (OriginalVariableLayout.binding (Entries arity) (s+1))

theorem source_outputs (input : OriginalFamilyInput.Input arity)
    (hv : OriginalFamilyInput.Valid arity input) (disequality : Bool) :
    ∃ bound, Nonempty (TM2OutputsInTime RawAffineRecognitionMachine.machine.computer
      (RawAffineRecognitionMachine.encoding.encode (OriginalFamilyPackingSource.fromSource arity input disequality))
      (some (encodingBoolBool.encode (answer arity input hv disequality))) bound) := by
  obtain ⟨bound,⟨run⟩⟩ := OriginalSystemMachine.source_outputs
    (OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input disequality))
    (OriginalAffineBranchMachine.descriptors_valid arity _ (OriginalFamilyInput.pack_valid arity input hv disequality))
    (combined arity input) (OriginalVariableLayout.binding (Entries arity) (s+1))
  have prepared := RawAffineRecognitionMachine.prepare.outputs (OriginalFamilyPackingSource.fromSource arity input disequality)
  rw [request_exact] at prepared
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ prepared run⟩⟩

theorem answer_correct (input : OriginalFamilyInput.Input arity)
    (hv : OriginalFamilyInput.Valid arity input) (disequality : Bool)
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
    (hG : ∀ i x, (input i x).Represents (G i x : ℂ)) :
    answer arity input hv disequality=true ↔
      AffineBranch.Shared G (OriginalFamilyInput.edge disequality) (algebraMap AlgebraicComplex ℂ) := by
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
  simpa only [w,OriginalAffineSystem.Bound,OriginalFamilyInput.sourceVertex_values,OriginalFamilyInput.sourceEdge_values] using
    bound_solution_iff arity input w

end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineRecognitionSource
