import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Loading
import Holant.Proofs.Algorithms.TransformRecognition.StructuredDovetail
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Completeness


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

def stage (r : Request) : Bool := (catalogue r).any NegativeCertificateMachine.check
abbrev catalogueEncoding := framedListEncoding NegativeCertificateMachine.encoding

namespace Traversal
noncomputable section
def anyTrue : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.any id) :=
  congrComputes (FiniteFold.computes encodingBoolBool encodingBoolBool 1 Bool.or false
    (fun b => by cases b <;> rfl)) (fun xs => by
      have h : ∀ (bs : List Bool) (b : Bool), bs.foldl Bool.or b = (b || bs.any id) := by
        intro bs
        induction bs with
        | nil => intro b; simp
        | cons a bs ih => intro b; simp [ih,Bool.or_assoc]
      simpa using h xs false)

def checks : Executes catalogueEncoding (framedListEncoding encodingBoolBool)
    (fun xs => xs.map NegativeCertificateMachine.check) := by
  let initial := Executes.ofComputes (pairComputes
    (constantComputes catalogueEncoding encodingBoolBool false) (identityComputes catalogueEncoding))
  let cell := (Executes.ofComputes
    (Wiring.secondComputes encodingBoolBool NegativeCertificateMachine.encoding)).comp
      NegativeCertificateMachine.executes
  exact initial.comp (Executes.mapList encodingBoolBool NegativeCertificateMachine.encoding
    encodingBoolBool (fun _ c => NegativeCertificateMachine.check c) cell)

def executes : Executes catalogueEncoding encodingBoolBool
    (fun xs => xs.any NegativeCertificateMachine.check) :=
  Executes.congr (checks.comp (Executes.ofComputes anyTrue))
    (fun xs => by simp only [List.any_map,Function.comp_def,id_eq])
end
end Traversal

noncomputable def executes : Executes encoding encodingBoolBool stage :=
  Generation.executes.comp Traversal.executes

theorem stage_fromSource {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) :
    stage (fromSource target S h) = (StructuredCatalogue.negative m n S.length h).any
      (NullstellensatzSearch.check target S) := by
  simp only [stage,catalogue_fromSource,List.any_map,Function.comp_def,
    NegativeCertificateMachine.check_fromCandidate]

theorem stage_eq_central {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    stage (fromSource target S h)=StructuredDovetail.negative target S h :=
  stage_fromSource target S h

noncomputable def source_outputs {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    TM2OutputsInTime executes.machine.computer (encoding.encode (fromSource target S h))
      (some (encodingBoolBool.encode (StructuredDovetail.negative target S h)))
      (executes.cost (fromSource target S h)) := by
  simpa only [stage_eq_central] using executes.outputs (fromSource target S h)

theorem accepted_witness {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) (hs : stage (fromSource target S h)=true) :
    ∃ c ∈ StructuredCatalogue.negative m n S.length h, NullstellensatzSearch.check target S c=true := by
  rw [stage_fromSource] at hs
  exact List.any_eq_true.mp hs

theorem source_sound {m n : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m n) (h : ℕ)
    (hs : stage (fromSource target S h)=true) :
    ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S, MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  obtain ⟨c,_,hc⟩ := accepted_witness target S h hs
  exact NullstellensatzSearch.check_sound target w ht S c hc

/-- Coverage of the finite stages, not a supplied validity/completeness premise
for the checker or a claim that the outer search has been implemented here. -/
theorem eventually_of_checked {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (c : NullstellensatzSearch.Candidate m n S.length)
    (hc : NullstellensatzSearch.check target S c=true) :
    ∃ H, ∀ h ≥ H, stage (fromSource target S h)=true := by
  obtain ⟨H,hH⟩ := StructuredCatalogue.covers_negative m n S.length c
  refine ⟨H,fun h hh => ?_⟩
  rw [stage_fromSource]
  exact List.any_eq_true.mpr ⟨c,hH h hh,hc⟩

/-- The existing mathematical completeness theorem supplies a checked
certificate; the central structural coverage puts it into ACTUAL generated
bytes at every sufficiently large height. There is no certificate parameter
in the statement, and the target descriptors are the original ones. -/
theorem eventually_iff_noComplex {m n : ℕ} (target : Fin m → RootCode)
    (w : Fin m → Holant.Tractable.AlgebraicComplex)
    (ht : ∀ i, (target i).Represents (w i : ℂ)) (S : EncodedSystem.System m n) :
    (∃ H, ∀ h ≥ H, stage (fromSource target S h)=true) ↔
      ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S,
        MvPolynomial.aeval x (EncodedSystem.polynomial (fun i => (w i : ℂ)) e)=0 := by
  constructor
  · rintro ⟨H,hH⟩
    exact source_sound target (fun i => (w i : ℂ)) ht S H (hH H le_rfl)
  · intro hn
    obtain ⟨c,hc⟩ := NullstellensatzSearch.exists_checked_of_noComplex w target ht S hn
    exact eventually_of_checked target S c hc

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
