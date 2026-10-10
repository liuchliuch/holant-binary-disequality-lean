import Holant.Proofs.Algorithms.TransformRecognition.PositiveCatalogueMachine.Programs
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Resources
import Holant.Proofs.Algorithms.TransformRecognition.CertificateStageMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCertificateStage
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Request := NegativeCatalogueMachine.Request
abbrev encoding := NegativeCatalogueMachine.encoding
abbrev fromSource {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) : Request :=
  NegativeCatalogueMachine.fromSource target S h

def catalogues (r : Request) : CertificateStageMachine.Input :=
  (PositiveCatalogueMachine.catalogue r,NegativeCatalogueMachine.catalogue r)

def stage (r : Request) : Option Bool := CertificateStageMachine.value (catalogues r)

noncomputable def generate : Executes encoding CertificateStageMachine.encoding catalogues :=
  PositiveCatalogueMachine.Generation.executes.pair NegativeCatalogueMachine.Generation.executes

noncomputable def executes : Executes encoding CertificateStageMachine.resultEncoding stage :=
  generate.comp CertificateStageMachine.executes

theorem catalogues_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    catalogues (fromSource target S h)=CertificateStageMachine.fromHeight target S h := by
  simp only [catalogues,PositiveCatalogueMachine.catalogue_fromSource,
    NegativeCatalogueMachine.catalogue_fromSource,CertificateStageMachine.fromHeight]

theorem stage_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    stage (fromSource target S h)=StructuredDovetail.stage target S h := by
  rw [stage,catalogues_fromSource,CertificateStageMachine.value_fromHeight]

noncomputable def source_outputs {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    TM2OutputsInTime executes.machine.computer (encoding.encode (fromSource target S h))
      (some (CertificateStageMachine.resultEncoding.encode (StructuredDovetail.stage target S h)))
      (executes.cost (fromSource target S h)) := by
  simpa only [stage_fromSource] using executes.outputs (fromSource target S h)

theorem transition_cost (r : Request) :
    executes.cost r = generate.cost r +
      2*((CertificateStageMachine.encoding.encode (catalogues r)).length+1) +
        CertificateStageMachine.executes.cost (catalogues r) := rfl

theorem primitive_bound (r : Request) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (encoding.encode r))) ≤
        executes.cost r*executes.machine.primitiveBudget := executes.primitive_bound r

theorem intermediate_bits (r : Request) (k : ℕ) (hk : k ≤ (executes.outputs r).steps)
    (c : executes.machine.Config)
    (hc : (fun p => p.bind executes.machine.computer.step)^[k]
      (some (initList executes.machine.computer (encoding.encode r)))=some c) :
    stackSize c.stk ≤ (encoding.encode r).length+executes.cost r*executes.machine.primitiveBudget := by
  have h := executes.machine.run_size_le (initList executes.machine.computer (encoding.encode r)) c k hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hk.trans (executes.outputs r).steps_le_m)) _)

theorem true_sound {m k : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (ha : stage (fromSource target S h)=some true) :
    ∃ z : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval z (EncodedSystem.polynomial w e)=0 :=
  StructuredDovetail.true_sound target w hw S h ((stage_fromSource target S h).symm.trans ha)

theorem false_sound {m k : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (ha : stage (fromSource target S h)=some false) :
    ¬∃ z : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval z (EncodedSystem.polynomial w e)=0 :=
  StructuredDovetail.false_sound target w hw S h ((stage_fromSource target S h).symm.trans ha)

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCertificateStage
