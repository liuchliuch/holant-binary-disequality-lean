import Holant.Proofs.Recognition.RuntimeSevenPrograms
import Holant.Proofs.Recognition.RuntimeSevenCriterionNormalization

/-! Exact positive and negative seven-clause source criterion for one physical
programme across all represented finite layouts. The programme internally
constructs profiles/pairings/templates, keeps the actual support and algebraic
packets, and reads the final Boolean from that retained output. Search-dependent
clocks and same-programme resources are asserted, not polynomial recognition.
No desired criterion, successful matrix, factorization, field presentation,
padded catalogue or stopping certificate is a source input. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open RuntimeSupportTable (Data original)
open RuntimeSevenPrograms
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def family (d : Data) := RuntimeSevenCriterionNormalization.family d.G
abbrev Profile (d : Data) := RuntimeSevenCriterionNormalization.Profile (arity:=d.arity)
def profileCode (d : Data) (p : Profile d) : RuntimeEOProfiles.Profile := List.ofFn (fun i => (p i).val)

theorem central_family (d : Data) : RuntimeEOViewDecision.family (eoData d none)=
    RuntimeSevenCriterionNormalization.family (RuntimeSevenCriterionNormalization.central d.G) := rfl

theorem completed_family (d : Data) (p : Profile d) :
    RuntimeEOViewDecision.family (eoData d (some (profileCode d p)))=
      RuntimeSevenCriterionNormalization.family
        (RuntimeSevenCriterionNormalization.completed (RuntimeSevenCriterionNormalization.native d.G) p) := by
  change (i : Fin d.count) → Fin (d.arity i+1) at p
  unfold RuntimeEOViewDecision.family RuntimeEOCriterionNormalization.family RuntimeSevenCriterionNormalization.family
  apply congrArg Set.range
  funext i
  change Fin d.count at i
  simp only [RuntimeEOViewDecision.arity,RuntimeEOViewDecision.signatures,RuntimeEOViewDecision.complete,
    RuntimeEOViewDecision.layers,eoData,tensorData,profileCode,Option.isSome_some,Option.getD_some,
    PositiveCertificateMachine.getD_ofFn,RuntimeEOView.arity,ite_true,RuntimeEOLiteralTable.viewSignature,
    RuntimeSevenCriterionNormalization.completedArity,RuntimeSevenCriterionNormalization.completed,
    RuntimeSevenCriterionNormalization.layers,RuntimeSevenCriterionNormalization.native]
  let pack (k : ℕ) : AnySignature AlgebraicComplex :=
    ⟨d.arity i+Holant.LocalDrafts.Hardness.SingleWeightCompletion.extra (d.arity i) k,
      Holant.LocalDrafts.Hardness.SingleWeightCompletion.completed (sourceKBasis.symm.action (d.G i)) k⟩
  change pack ((List.ofFn (fun j => (p j).val)).getD i.val 0)=pack (p i).val
  exact congrArg pack (PositiveCertificateMachine.getD_ofFn (fun j => (p j).val) i 0)

theorem oneSided_correct (d : Data) : oneSided (details d)=true ↔ OneSidedAlternative (preprocess (family d)) := by
  change ((RuntimeSupportFlags.side false (RuntimeSupportTable.output d) ||
    RuntimeSupportFlags.side true (RuntimeSupportTable.output d)) &&
      (RuntimeEOViewDecision.output (eoData d none)).1)=true ↔
        OneSidedAlternative (preprocess (RuntimeSevenCriterionNormalization.family d.G))
  rw [RuntimeSevenCriterionNormalization.oneSided_iff]
  simp only [Bool.and_eq_true,Bool.or_eq_true,RuntimeEOViewDecision.output_correct,central_family]
  apply and_congr_left
  intro _
  simp only [RuntimeSupportFlags.side_correct,CommonOneSided,RuntimeSevenCriterionNormalization.family,
    Set.forall_mem_range,RuntimeSevenCriterionNormalization.native,UniformKSupport.signHolds,
    Bool.false_eq_true,ite_false,ite_true]

theorem bothSigns_correct (d : Data) :
    (!RuntimeSupportFlags.side false (RuntimeSupportTable.output d) &&
      !RuntimeSupportFlags.side true (RuntimeSupportTable.output d))=true ↔
      BothChargeSigns (RuntimeSevenCriterionNormalization.family (RuntimeSevenCriterionNormalization.native d.G)) := by
  have hb : ∀b : Bool,(!b)=true ↔ ¬b=true := by intro b; cases b <;> simp
  simp only [Bool.and_eq_true,hb,RuntimeSupportFlags.side_correct,UniformKSupport.signHolds,
    Bool.false_eq_true,ite_false,ite_true,BothChargeSigns,RuntimeSevenCriterionNormalization.family,
    RuntimeSevenCriterionNormalization.native,Set.mem_range]
  push_neg
  constructor
  · rintro ⟨⟨i,x,hx,hn⟩,⟨j,y,hy,hp⟩⟩
    exact ⟨⟨_,⟨i,rfl⟩,x,hx,hn⟩,⟨_,⟨j,rfl⟩,y,hy,hp⟩⟩
  · rintro ⟨⟨f,⟨i,rfl⟩,x,hx,hn⟩,⟨g,⟨j,rfl⟩,y,hy,hp⟩⟩
    exact ⟨⟨i,x,hx,hn⟩,⟨j,y,hy,hp⟩⟩

theorem profile_code_mem (d : Data) (p : Profile d) : profileCode d p∈profiles d :=
  RuntimeEOProfiles.source_mem d.arity d.input p

theorem profile_accepted_correct (d : Data) (p : Profile d) :
    profileAccepted (profileOutput d (profileCode d p))=true ↔
      (∀i,Signature.SingleLayer (RuntimeSevenCriterionNormalization.native d.G i) (RuntimeSevenCriterionNormalization.layers p i)) ∧
      EOTract (preprocess (RuntimeSevenCriterionNormalization.family
        (RuntimeSevenCriterionNormalization.completed (RuntimeSevenCriterionNormalization.native d.G) p))) := by
  change ((RuntimeLayerProfile.output (RuntimeLayerProfile.source d (profileCode d p))).1 &&
    (RuntimeEOViewDecision.output (eoData d (some (profileCode d p)))).1)=true ↔ _
  rw [Bool.and_eq_true,RuntimeLayerProfile.output_correct,RuntimeEOViewDecision.output_correct,completed_family]
  simp only [profileCode,PositiveCertificateMachine.getD_ofFn,RuntimeSevenCriterionNormalization.layers,
    RuntimeSevenCriterionNormalization.native]

theorem profiles_correct (d : Data) : (allProfiles d).any profileAccepted=true ↔
    ∃p : Profile d,
      (∀i,Signature.SingleLayer (RuntimeSevenCriterionNormalization.native d.G i) (RuntimeSevenCriterionNormalization.layers p i)) ∧
      EOTract (preprocess (RuntimeSevenCriterionNormalization.family
        (RuntimeSevenCriterionNormalization.completed (RuntimeSevenCriterionNormalization.native d.G) p))) := by
  simp only [allProfiles,List.any_map,List.any_eq_true,Function.comp_def]
  constructor
  · rintro ⟨raw,hr,hflag⟩
    let p : Profile d := RuntimeEOProfiles.reify d.arity d.input raw hr
    have he : profileCode d p=raw := RuntimeEOProfiles.reify_exact d.arity d.input raw hr
    rw [←he] at hflag
    exact ⟨p,(profile_accepted_correct d p).mp hflag⟩
  · rintro ⟨p,hp⟩
    exact ⟨profileCode d p,profile_code_mem d p,(profile_accepted_correct d p).mpr hp⟩

theorem singleWeight_correct (d : Data) : singleWeight (details d)=true ↔
    SingleWeightAlternative (preprocess (family d)) := by
  change ((!RuntimeSupportFlags.side false (RuntimeSupportTable.output d) &&
    !RuntimeSupportFlags.side true (RuntimeSupportTable.output d)) &&
      (allProfiles d).any profileAccepted)=true ↔
        SingleWeightAlternative (preprocess (RuntimeSevenCriterionNormalization.family d.G))
  rw [RuntimeSevenCriterionNormalization.singleWeight_iff,Bool.and_eq_true,bothSigns_correct,profiles_correct]

theorem matching_correct (d : Data) : matching (details d)=true ↔ MatchingAlternative (family d) :=
  RuntimeFourDecision.matching_retained (tensorData d)
theorem four_correct (d : Data) : four (details d)=true ↔ TractX (family d) :=
  RuntimeFourDecision.ordinary_correct (tensorData d)

theorem output_correct (d : Data) : (output d).1=true ↔ Tract (family d) := by
  change summary (details d)=true ↔ Tract (RuntimeSevenCriterionNormalization.family d.G)
  rw [RuntimeSevenCriterionNormalization.tract_iff]
  simp only [summary,Bool.or_eq_true,oneSided_correct,singleWeight_correct,matching_correct,four_correct,or_assoc,family]

theorem output_false_iff (d : Data) : (output d).1=false ↔ ¬Tract (family d) := by
  have hb : ∀b : Bool,b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,output_correct]

/-- Quantifier order is one programme before every finite arity layout and
represented RootCode input; this is not merely a layout-indexed machine family. -/
theorem uniform_source : ∃M : BinaryCompose.Machine,∀d : Data,
    Nonempty (TM2OutputsInTime M.computer (OriginalFamilyPackingMachine.encoding.encode (original d))
      (some (outputEncoding.encode (output d))) (executes.cost d)) ∧
    ((output d).1=true ↔ Tract (family d)) ∧ ((output d).1=false ↔ ¬Tract (family d)) :=
  ⟨executes.machine,fun d => ⟨⟨executes.outputs d⟩,output_correct d,output_false_iff d⟩⟩

theorem resources (d : Data) :
    primitiveCost executes.machine (executes.outputs d).steps
      (some (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d)))) ≤
      executes.cost d*executes.machine.primitiveBudget ∧
    ∀k,k≤(executes.outputs d).steps → ∀cfg : executes.machine.Config,
      (fun st => st.bind executes.machine.computer.step)^[k]
        (some (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d))))=some cfg →
      stackSize cfg.stk ≤ (OriginalFamilyPackingMachine.encoding.encode (original d)).length+
        executes.cost d*executes.machine.primitiveBudget := by
  constructor
  · exact (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (executes.outputs d).steps_le_m)
  · intro k hk cfg hc
    have h := executes.machine.run_size_le
      (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d))) cfg k hc
    rw [Machine.size_init] at h
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hk.trans (executes.outputs d).steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenDecision
