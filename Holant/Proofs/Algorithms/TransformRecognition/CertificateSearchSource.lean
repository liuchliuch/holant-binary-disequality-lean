import Holant.Proofs.Algorithms.TransformRecognition.CertificateSearchLoop


namespace Holant.LocalDrafts.MainChain.TransformRecognition.CertificateSearchSource
open Turing Computability Holant.Algebraic Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition

theorem advance_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h n : ℕ) :
    CertificateSearchLoop.advance (OriginalCertificateStage.fromSource target S h) n =
      OriginalCertificateStage.fromSource target S (h+n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CertificateSearchLoop.advance,Function.iterate_succ_apply']
    change CertificateSearchLoop.bump
      (CertificateSearchLoop.advance (OriginalCertificateStage.fromSource target S h) n) = _
    rw [ih]
    rfl

theorem first_before {m k : ℕ} (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot)
    (j : ℕ) (hj : j < Nat.find (StructuredDovetail.terminates target oneSlot negSlot S hv)) :
    OriginalCertificateStage.stage
      (CertificateSearchLoop.advance
        (OriginalCertificateStage.fromSource target (EncodedGuard.augment oneSlot negSlot S) 0) j)=none := by
  rw [advance_fromSource,Nat.zero_add,OriginalCertificateStage.stage_fromSource]
  have hn := Nat.find_min (StructuredDovetail.terminates target oneSlot negSlot S hv) hj
  cases hs : StructuredDovetail.stage target (EncodedGuard.augment oneSlot negSlot S) j with
  | none => rfl
  | some b => exact False.elim (hn (by simp [hs]))

/-- A real run of one fixed finite program. Neither the certificate nor the
successful stage, a common primitive element or a solution is an input. -/
theorem outputs {m k : ℕ} (target : Fin m → RootCode) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    ∃ ticks, Nonempty (TM2OutputsInTime CertificateSearchLoop.machine.computer
      (OriginalCertificateStage.encoding.encode
        (OriginalCertificateStage.fromSource target (EncodedGuard.augment oneSlot negSlot S) 0))
      (some (encodingBoolBool.encode (StructuredDovetail.answer target oneSlot negSlot S hv))) ticks) := by
  refine ⟨_,⟨CertificateSearchLoop.outputs_of_first
    (Nat.find (StructuredDovetail.terminates target oneSlot negSlot S hv))
    _ _ ?_ ?_⟩⟩
  · exact first_before target oneSlot negSlot S hv
  · rw [advance_fromSource,Nat.zero_add,OriginalCertificateStage.stage_fromSource]
    exact StructuredDovetail.answer_stage target oneSlot negSlot S hv

theorem outputs_correct {m k : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (target i).Represents (w i)) (oneSlot negSlot : Fin m)
    (S : EncodedSystem.System m (5+k)) (hv : CertificateDovetail.Valid target oneSlot negSlot) :
    ∃ b ticks, Nonempty (TM2OutputsInTime CertificateSearchLoop.machine.computer
      (OriginalCertificateStage.encoding.encode
        (OriginalCertificateStage.fromSource target (EncodedGuard.augment oneSlot negSlot S) 0))
      (some (encodingBoolBool.encode b)) ticks) ∧
      (b=true ↔ ∃ z : Fin (5+k) → ℂ, ∀ e ∈ EncodedGuard.augment oneSlot negSlot S,
        MvPolynomial.aeval z (EncodedSystem.polynomial w e)=0) := by
  obtain ⟨ticks,ht⟩ := outputs target oneSlot negSlot S hv
  exact ⟨_,ticks,ht,StructuredDovetail.answer_correct target w hw oneSlot negSlot S hv⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.CertificateSearchSource
