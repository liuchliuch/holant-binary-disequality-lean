import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Source
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Generators


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Enumeration
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open ComplexIsolation CertificateMachine
open RootSearchDriver (cross mem_cross)
open StructuredCatalogue (Covers covers_cross covers_map)

def tags (_h : ℕ) : List Bool := [false,true]
def wires (h : ℕ) : List EvidenceWire :=
  cross (tags h) (cross (StructuredCatalogue.polynomials h)
    (cross (StructuredCatalogue.polynomials h) (cross (StructuredCatalogue.polynomials h)
      (cross (StructuredCatalogue.polynomials h) (RootSearchDriver.certificates h)))))
def candidates (h : ℕ) : List Evidence := (wires h).map evidenceUnwire

private theorem cross_length {A B : Type*} (xs : List A) (ys : List B) :
    (cross xs ys).length=xs.length*ys.length := by
  induction xs with
  | nil => simp only [cross,List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | cons a xs ih =>
    change (ys.map (fun b => (a,b)) ++ cross xs ys).length=(xs.length+1)*ys.length
    simp only [List.length_append,List.length_map,ih,Nat.add_mul,Nat.one_mul]
    omega

/-- Literal materialized size, with duplicates counted. This is deliberately
large; the physical cost charges serialization of the whole product. -/
theorem candidates_length (h : ℕ) :
    (candidates h).length=2*(StructuredCatalogue.polynomials h).length^4*
      (RootSearchDriver.certificates h).length := by
  simp only [candidates,List.length_map,wires,cross_length,tags,List.length_cons,List.length_nil]
  ring

theorem covers_tags : Covers tags := by
  intro b
  exact ⟨0,fun _ _ => by cases b <;> simp [tags]⟩

theorem covers_wires : Covers wires :=
  covers_cross covers_tags (covers_cross StructuredCatalogue.covers_polynomials
    (covers_cross StructuredCatalogue.covers_polynomials
      (covers_cross StructuredCatalogue.covers_polynomials
        (covers_cross StructuredCatalogue.covers_polynomials StructuredCatalogue.covers_certificates))))

/-- Every literal Evidence, including both tags and all FOUR unbounded lists,
occurs at every sufficiently large height. Coverage is independent of check. -/
theorem covers : Covers candidates :=
  covers_map covers_wires evidenceUnwire (fun e => ⟨evidenceWire e,evidenceUnwire_wire e⟩)

theorem codec_valid (h : ℕ) (e : Evidence) (_he : e ∈ candidates h) :
    evidenceEncoding.decode (evidenceEncoding.encode e)=some e := evidenceEncoding.decode_encode e

theorem word_coverage (e : Evidence) :
    ∃ H, ∀ h ≥ H, evidenceEncoding.encode e ∈ (candidates h).map evidenceEncoding.encode := by
  obtain ⟨H,hH⟩ := covers e
  exact ⟨H,fun h hh => List.mem_map.mpr ⟨e,hH h hh,rfl⟩⟩

noncomputable section

def tagsExecutes : Executes encodingNatBool (framedListEncoding encodingBoolBool) tags :=
  Executes.ofComputes (constantComputes encodingNatBool (framedListEncoding encodingBoolBool) [false,true])

/-- The four-list constructor reuses the ACTUAL bounded sparse-polynomial
program from the ideal search; no polynomial list producer is duplicated. -/
def wiresExecutes : Executes encodingNatBool (framedListEncoding evidenceWireEncoding) wires :=
  NegativeCatalogueMachine.Programs.cross encodingBoolBool evidenceTail₁Encoding tagsExecutes
    (NegativeCatalogueMachine.Programs.cross polynomialEncoding evidenceTail₂Encoding
      NegativeCatalogueMachine.Programs.polynomials
      (NegativeCatalogueMachine.Programs.cross polynomialEncoding evidenceTail₃Encoding
        NegativeCatalogueMachine.Programs.polynomials
        (NegativeCatalogueMachine.Programs.cross polynomialEncoding evidenceTail₄Encoding
          NegativeCatalogueMachine.Programs.polynomials
          (NegativeCatalogueMachine.Programs.cross polynomialEncoding certificateEncoding
            NegativeCatalogueMachine.Programs.polynomials NegativeCatalogueMachine.Programs.certificates))))

def unwireComputes : Computes evidenceWireEncoding evidenceEncoding evidenceUnwire :=
  recode (identityComputes evidenceWireEncoding) id (fun _ => rfl)
    (fun w => by simp only [id_eq,evidenceEncoding,evidenceWire_unwire])

def executes : Executes encodingNatBool Scan.evidenceListEncoding candidates :=
  wiresExecutes.comp (Executes.ofComputes (WireLists.mapComputes evidenceWireEncoding evidenceEncoding
    evidenceUnwire unwireComputes))

def outputs (h : ℕ) : TM2OutputsInTime executes.machine.computer (encodingNatBool.encode h)
    (some (Scan.evidenceListEncoding.encode (candidates h))) (executes.cost h) := executes.outputs h

theorem primitives (h : ℕ) :
    primitiveCost executes.machine (outputs h).steps
      (some (initList executes.machine.computer (encodingNatBool.encode h))) ≤
      executes.cost h*executes.machine.primitiveBudget := executes.primitive_bound h

theorem prefix_bits (h j : ℕ) (hj : j ≤ (outputs h).steps) (c : executes.machine.Config)
    (hc : (fun p => p.bind executes.machine.computer.step)^[j]
      (some (initList executes.machine.computer (encodingNatBool.encode h)))=some c) :
    stackSize c.stk ≤ (encodingNatBool.encode h).length+executes.cost h*executes.machine.primitiveBudget := by
  have hs := executes.machine.run_size_le (initList executes.machine.computer (encodingNatBool.encode h)) c j hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hj.trans (outputs h).steps_le_m)) _)
end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Enumeration
