import Holant.Proofs.AlgebraicRecognition.WitnessOutput.Programs
import Holant.Proofs.Algorithms.TransformRecognition.CertificateSearchSource


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
open Holant Holant.Tractable Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open CommonFieldMachine (Executes)
open PositiveCertificateMachine

def stage (r : PositiveCatalogueMachine.Request) : List Output :=
  scan (PositiveCatalogueMachine.catalogue r)
def first (r : PositiveCatalogueMachine.Request) : Option Output := (stage r).head?

theorem head_scan_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (cs : List (PositiveWitnessSearch.Candidate m k)) :
    (scan (cs.map (fromSource target S))).head? =
      (cs.find? (PositiveWitnessSearch.check target S)).map ofCandidate := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    cases ha : PositiveWitnessSearch.check target S a with
    | false =>
      simpa [scan, accepted, check_fromSource, emit_fromSource, ha, List.find?_cons] using ih
    | true =>
      simp [scan, accepted, check_fromSource, emit_fromSource, ha, List.find?_cons]

theorem first_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    first (PositiveCatalogueMachine.fromSource target S h) =
      (StructuredWitness.atHeight target S h).map ofCandidate := by
  unfold first stage
  rw [PositiveCatalogueMachine.catalogue_fromSource]
  exact head_scan_fromSource target S _

/-- Coverage ranges over all algebraic input coefficients and solution values;
no fixed presented field is a completeness premise. These are semantic facts
used to prove coverage, never supplied to any runtime program. -/
theorem eventually_isSome {m k : ℕ} (w : Fin m → AlgebraicComplex)
    (target : Fin m → RootCode) (ht : ∀ i, (target i).Represents (w i : ℂ))
    (S : EncodedSystem.System m (5+k)) (y : Fin (5+k) → AlgebraicComplex)
    (hy : ∀ e ∈ S, MvPolynomial.aeval (fun j => (y j : ℂ))
      (EncodedSystem.polynomial (fun i => (w i : ℂ)) e) = 0)
    (hg : y (Fin.castAdd k 4) *
      (y (Fin.castAdd k 0) * y (Fin.castAdd k 3) -
        y (Fin.castAdd k 1) * y (Fin.castAdd k 2)) = 1) :
    ∃ H, ∀ h ≥ H, (first (PositiveCatalogueMachine.fromSource target S h)).isSome = true := by
  obtain ⟨j, hj⟩ := PositiveWitnessSearch.eventually_some w target ht S y hy hg
  obtain ⟨a, ha⟩ := hj j le_rfl
  have hc : PositiveWitnessSearch.check target S a = true :=
    PositiveWitnessSearch.first_checked target S _ a ha
  obtain ⟨H, hH⟩ := StructuredCatalogue.covers_positive m k a
  refine ⟨H, fun h hh => ?_⟩
  rw [first_fromSource, Option.isSome_map]
  change ((StructuredCatalogue.positive m k h).find?
    (PositiveWitnessSearch.check target S)).isSome = true
  rw [List.find?_isSome]
  exact ⟨a, hH h hh, hc⟩

def previous (r : CertificateSearchLoop.Request) : CertificateSearchLoop.Request :=
  { r with height := r.height - 1 }

theorem previous_bump (r : CertificateSearchLoop.Request) :
    previous (CertificateSearchLoop.bump r) = r := by
  simp [previous, CertificateSearchLoop.bump]

theorem previous_source {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (n : ℕ) :
    previous (CertificateSearchLoop.advance (OriginalCertificateStage.fromSource target S 0) (n+1)) =
      PositiveCatalogueMachine.fromSource target S n := by
  rw [CertificateSearchSource.advance_fromSource]
  simp [previous, OriginalCertificateStage.fromSource, PositiveCatalogueMachine.fromSource,
    NegativeCatalogueMachine.fromSource]

def sourceOutput {m k : ℕ} (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    Option Output := (StructuredWitness.candidate target oneSlot negSlot S hv).map ofCandidate

theorem sourceOutput_isSome {m k : ℕ} (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    (sourceOutput target oneSlot negSlot S hv).isSome = true ↔
      StructuredDovetail.answer target oneSlot negSlot S hv = true := by
  simpa only [sourceOutput, Option.isSome_map] using
    StructuredWitness.candidate_isSome target oneSlot negSlot S hv

noncomputable section

def stageExecutes : Executes PositiveCatalogueMachine.encoding outputsEncoding stage :=
  PositiveCatalogueMachine.Generation.executes.comp scanExecutes

def firstExecutes : Executes PositiveCatalogueMachine.encoding resultEncoding first :=
  stageExecutes.comp (Executes.ofComputes headComputes)

/-- Only the binary height changes; all original roots/equations and counts
are copied using the existing faithful request projections. -/
def previousExecutes : Executes CertificateSearchLoop.requestEncoding
    CertificateSearchLoop.requestEncoding previous := by
  let h := (pairComputes NegativeCatalogueMachine.Access.height
    (constantComputes CertificateSearchLoop.requestEncoding encodingNatBool 1)).andThen
      Endpoints.subtractComputes
  let context := pairComputes NegativeCatalogueMachine.Access.equations h
  let roots := pairComputes NegativeCatalogueMachine.Access.targets context
  let variableSlots := pairComputes NegativeCatalogueMachine.Access.variables roots
  let full := pairComputes NegativeCatalogueMachine.Access.coefficients variableSlots
  exact Executes.recode (Executes.ofComputes full) id (fun _ => rfl) (fun _ => rfl)

def finalExecutes : Executes CertificateSearchLoop.encoding resultEncoding
    (fun s => first (previous s.1)) :=
  ((Executes.ofComputes (Wiring.firstComputes CertificateSearchLoop.requestEncoding
    CertificateSearchLoop.resultEncoding)).comp previousExecutes).comp firstExecutes

/-- Same existing controller, both existing checkers, and original catalogue.
Only the final Boolean projection is replaced by physical witness extraction. -/
def machine : Machine :=
  (CertificateSearchLoop.prepare.machine.compose CertificateSearchLoop.loop).compose finalExecutes.machine

def totalBound (n : ℕ) (r : CertificateSearchLoop.Request) (b : Bool) : ℕ :=
  CertificateSearchLoop.prepare.time.eval (CertificateSearchLoop.requestEncoding.encode r).length +
    2 * ((CertificateSearchLoop.encoding.encode (r, none)).length + 1) +
    CertificateSearchLoop.bound n (r, none) +
    2 * ((CertificateSearchLoop.encoding.encode (CertificateSearchLoop.advance r (n+1), some b)).length + 1) +
    finalExecutes.cost (CertificateSearchLoop.advance r (n+1), some b)

/-- Prop-valued run packaging permits elimination of the proved run's ticks
without a noncomputable choice. The machine contains neither n nor a witness.
All local stopping premises are discharged in outputs below. -/
theorem outputs_at_first (n : ℕ) (r : CertificateSearchLoop.Request) (b : Bool)
    (before : ∀ j < n, OriginalCertificateStage.stage (CertificateSearchLoop.advance r j) = none)
    (last : OriginalCertificateStage.stage (CertificateSearchLoop.advance r n) = some b) :
    Nonempty (TM2OutputsInTime machine.computer (CertificateSearchLoop.requestEncoding.encode r)
      (some (resultEncoding.encode (first (previous (CertificateSearchLoop.advance r (n+1))))))
      (totalBound n r b)) := by
  obtain ⟨ticks, hticks, hr⟩ := CertificateSearchLoop.run n r none b before last
  let hloop : TM2OutputsInTime CertificateSearchLoop.loop.computer
      (CertificateSearchLoop.encoding.encode (r, none))
      (some (CertificateSearchLoop.encoding.encode (CertificateSearchLoop.advance r (n+1), some b)))
      (CertificateSearchLoop.bound n (r, none)) := {
    steps := ticks
    evals_in_steps := by
      change StackProtocol.RunsExactly CertificateSearchLoop.loop.computer.step
        (initList CertificateSearchLoop.loop.computer (CertificateSearchLoop.encoding.encode (r, none)))
        (haltList CertificateSearchLoop.loop.computer
          (CertificateSearchLoop.encoding.encode (CertificateSearchLoop.advance r (n+1), some b))) ticks
      rw [show initList CertificateSearchLoop.loop.computer
        (CertificateSearchLoop.encoding.encode (r, none)) =
        CommonFieldMachine.ReturningLoop.ready CertificateSearchLoop.body.machine
          (.inl CertificateSearchLoop.body.machine.main)
          (.inl CertificateSearchLoop.body.machine.input)
          (CertificateSearchLoop.encoding.encode (r, none)) from
        CommonFieldMachine.ReturningLoop.initial CertificateSearchLoop.body.machine _]
      exact hr
    steps_le_m := hticks }
  let start := Machine.compose_correct _ _ _ _ _ _ _ (CertificateSearchLoop.prepare.outputs r) hloop
  exact ⟨Machine.compose_correct _ _ _ _ _ _ _ start
    (finalExecutes.outputs (CertificateSearchLoop.advance r (n+1), some b))⟩

/-- Physical original-source witness production, including the negative
answer none. No solution, accepted candidate, field presentation, stopping
height or execution-cost certificate is present in the encoded input. -/
theorem outputs {m k : ℕ} (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    ∃ ticks, Nonempty (TM2OutputsInTime machine.computer
      (CertificateSearchLoop.requestEncoding.encode
        (OriginalCertificateStage.fromSource target (EncodedGuard.augment oneSlot negSlot S) 0))
      (some (resultEncoding.encode (sourceOutput target oneSlot negSlot S hv))) ticks) := by
  let n := Nat.find (StructuredDovetail.terminates target oneSlot negSlot S hv)
  let r := OriginalCertificateStage.fromSource target (EncodedGuard.augment oneSlot negSlot S) 0
  let b := StructuredDovetail.answer target oneSlot negSlot S hv
  have before : ∀ j < n, OriginalCertificateStage.stage (CertificateSearchLoop.advance r j) = none := by
    intro j hj
    exact CertificateSearchSource.first_before target oneSlot negSlot S hv j hj
  have last : OriginalCertificateStage.stage (CertificateSearchLoop.advance r n) = some b := by
    rw [CertificateSearchSource.advance_fromSource, Nat.zero_add, OriginalCertificateStage.stage_fromSource]
    exact StructuredDovetail.answer_stage target oneSlot negSlot S hv
  have he : first (previous (CertificateSearchLoop.advance r (n+1))) =
      sourceOutput target oneSlot negSlot S hv := by
    rw [previous_source, first_fromSource]
    rfl
  refine ⟨totalBound n r b, ?_⟩
  simpa only [he] using outputs_at_first n r b before last

end

/-- The physical output is the SAME original first accepted candidate. The
root, matrices, inverse, scalar slots and all variable bytes are determined
by ofCandidate; the semantic root is used only in this soundness theorem. -/
theorem returned_sound {m k : ℕ} (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot)
    (w : Fin m → AlgebraicComplex) (hw : ∀ i, (target i).Represents (w i : ℂ))
    (o : Output) (ho : sourceOutput target oneSlot negSlot S hv = some o) :
    ∃ a : PositiveWitnessSearch.Candidate m k,
      StructuredWitness.candidate target oneSlot negSlot S hv = some a ∧ o = ofCandidate a ∧
      ∃ θ : AlgebraicComplex, o.root.Represents (θ : ℂ) ∧
        θ^(a.1.1+1) = PowerArithmetic.decode θ a.1.2.1 ∧
        (Holant.Kernel.mul
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.matrixCode a.1.2.2.2.2 u v))
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.inverseCode a.1.2.1 a.1.2.2.2.2 u v)) =
            Holant.Signature.equality ∧
         Holant.Kernel.mul
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.inverseCode a.1.2.1 a.1.2.2.2.2 u v))
          (fun u v => PowerArithmetic.decode θ (MatrixWitness.matrixCode a.1.2.2.2.2 u v)) =
            Holant.Signature.equality) ∧
        ∀ e ∈ EncodedGuard.augment oneSlot negSlot S,
          MvPolynomial.aeval (fun i => (PowerArithmetic.decode θ (a.1.2.2.2.2 i) : ℂ))
            (EncodedSystem.polynomial (fun i => (w i : ℂ)) e) = 0 := by
  change (StructuredWitness.candidate target oneSlot negSlot S hv).map ofCandidate = some o at ho
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.mp ho
  subst o
  have hc := StructuredWitness.candidate_sound target oneSlot negSlot S hv a ha
  obtain ⟨θ, hr, hrel, hinv, heq⟩ := StructuredWitness.emit_sound target w hw
    (EncodedGuard.augment oneSlot negSlot S) a hc
  exact ⟨a, ha, rfl, θ, hr, hrel, hinv, heq⟩

end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
