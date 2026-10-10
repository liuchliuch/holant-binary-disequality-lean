import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Counting.RawGraphMachine.Frontend
import Holant.Proofs.Counting.NetworkSemantics
import Holant.Proofs.Algorithms.CountingCircuitAdapter
import Holant.Proofs.CountingMachines.VerifierCircuit.Source
import Holant.Proofs.CountingMachines.AnswerDecoder.Bounds
import Holant.Proofs.Counting.Hardness
import Holant.Proofs.Closure.PhysicalCosts
import Holant.Proofs.Closure.ProgrammeCompose

/-! A genuine counted-verifier source for the cubic-sign phase in an actual
ordinary family. Every gate is compiled to the original cubic/Eq4/pin rows;
the physical postprocessor divides by two to the actual NAND occurrence count.
The source's fixed coefficient field and validated ordered graph codec are
unchanged. This includes empty graphs, repeated operands and unused choices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicSource
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.CountingBridge
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace M
export OrdinaryNegativeCubicGadgets (gate gate_exact)
end M
namespace B
export Holant.LocalDrafts.CountingHardness.RawCompiler (validated)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine (computes)
export Holant.LocalDrafts.CountingHardness.NetworkSemantics (compile_denote)
end B
namespace V
export CountingCircuitAdapter (query queryComputes query_value)
end V
namespace D
export AnswerDecoder (natural computes natural_natCast)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable (F : FixedField K d) (H : (i : Fin s) → Signature K (a i.val))
variable (j e p₀ p₁ : Fin s)
variable (hj : (⟨a j.val,H j⟩ : AnySignature K)=⟨3,OrdinaryNegativeCubicCore.cubic⟩)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h₀ : (⟨a p₀.val,H p₀⟩ : AnySignature K)=⟨1,Gates.pin false⟩)
variable (h₁ : (⟨a p₁.val,H p₁⟩ : AnySignature K)=⟨1,Gates.pin true⟩)

abbrev templates (i : ℕ) := (M.gate H j e p₀ p₁ hj he h₀ h₁ i).template
omit [Algebra ℚ K] in
theorem templates_valid : ∀i<5,(templates H j e p₀ p₁ hj he h₀ h₁ i).WellFormed s 1 a :=
  fun i _=>(M.gate H j e p₀ p₁ hj he h₀ h₁ i).labels.wellFormed

abbrev tables := QuaternaryOrdinaryCompanion.tables F H
abbrev value := (tables F H).evaluate F
abbrev gateTables := QuaternaryOrdinaryCompanion.tables F (Gates.signatures (K:=K))
abbrev gateValue := (gateTables F).evaluate F
abbrev gateEncoding := RawClosedNetwork.validatedEncoding 5 1 Gates.arity

theorem template_exact (i : Fin 5) :
    ((templates H j e p₀ p₁ hj he h₀ h₁ i.val).network
      (templates_valid H j e p₀ p₁ hj he h₀ h₁ i.val i.isLt)
      (fun k x=>F.decode ((tables F H).vertex k x))
      (fun k b c=>F.decode ((tables F H).edge k b c))).denote=
        (if i.val=4 then (2 : K) else 1) • Gates.signatures i := by
  simp only [tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  exact (M.gate H j e p₀ p₁ hj he h₀ h₁ i.val).template_exact.trans
    (M.gate_exact H j e p₀ p₁ hj he h₀ h₁ i)

/-- The exact multiplicity correction is executed by the existing scalar
power machine; in particular its exponent is the emitted input's label count. -/
def gateControlled : LengthControlledOracleReduction gateEncoding F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding (gateValue F) (value F H) := by
  let r := Holant.LocalDrafts.Hardness.ControlledCap.controlledSubstitution F
    (templates H j e p₀ p₁ hj he h₀ h₁)
    (templates_valid H j e p₀ p₁ hj he h₀ h₁) (tables F H)
    (fun i x=>F.decode.symm (Gates.signatures i x)) 4 (2 : K) (by norm_num)
    (fun i=>by simpa only [LinearEquiv.apply_symm_apply] using
      template_exact F H j e p₀ p₁ hj he h₀ h₁ i)
  exact r

theorem gate_value (r : ExactSignatureTables.Input 5 1 Gates.arity) :
    gateValue F r=(r.val.realize r.property (Gates.signatures (K:=K))
      (fun _ : Fin 1=>Signature.equality)).denote Fin.elim0 := by
  unfold gateValue
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [gateTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def query (w : SharpPWitness ea count) (x : α) :
    ExactSignatureTables.Input 5 1 Gates.arity :=
  ⟨(B.validated (V.query w x)).val,(B.validated (V.query w x)).property⟩
def queryComputes (w : SharpPWitness ea count) : Computes ea gateEncoding (query w) :=
  recode ((V.queryComputes w).andThen B.computes) id (fun _=>rfl) (fun _=>rfl)

theorem query_value (w : SharpPWitness ea count) (x : α) :
    gateValue F (query w x)=(count x : K) := by
  rw [gate_value]
  change ((Holant.LocalDrafts.CountingHardness.RawCompiler.compile (V.query w x)).realize
    (Holant.LocalDrafts.CountingHardness.RawCompiler.compile_wellFormed (V.query w x))
    (Holant.LocalDrafts.CountingHardness.GateAlphabet.signatures (K:=K))
    (fun _ : Fin 1=>Signature.equality)).denote Fin.elim0=_
  rw [B.compile_denote,←V.query_value w x]
  simp [Holant.LocalDrafts.CountingHardness.CircuitInstance.value,
    countAccepted]

def verifierControlled (w : SharpPWitness ea count) : LengthControlledOracleReduction
    ea encodingNatBool gateEncoding F.encoding count (gateValue F) :=
  controlledOneQueryOfEq (queryComputes w) (D.computes F) ((gateTables F).outputBound F)
    count (fun x=>by
      change count x=D.natural F (gateValue F (query w x))
      rw [query_value,D.natural_natCast])

/-- No evaluator, supplied gate gadget, or assumed hardness is a premise. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding count (value F H) :=
  Programme.compose (verifierControlled F w) (gateControlled F H j e p₀ p₁ hj he h₀ h₁)

def physical (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding count (value F H) :=
  PhysicalProgramme.ofControlled (source F H j e p₀ p₁ hj he h₀ h₁ w)

include j e p₀ p₁ hj he h₀ h₁ in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding (value F H) := by
  intro α ea count w
  exact ⟨(source F H j e p₀ p₁ hj he h₀ h₁ w).reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicSource
end
