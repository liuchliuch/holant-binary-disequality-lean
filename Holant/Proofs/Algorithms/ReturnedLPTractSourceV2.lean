import Holant.Proofs.Algorithms.ReturnedLPOneSidedSource
import Holant.Proofs.Algorithms.ReturnedLPSingleWeightSource
import Holant.Proofs.Algorithms.TractCoreSource
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Additive V2: actual_output is a data-valued `def`, preserving its
TM2OutputsInTime witness and SAME programme. The seven positive source clauses on a fixed original
indexed family G contained in its original family Gamma. The structural
inputs are original membership and Tract Gamma. The literal range of G and
its finiteness are produced internally for the four TractX branches.

Clauses (1) and (2) use the returned-LP ordinary equality-graph programmes;
clause (4) uses the existing matching programme. Clauses (3), (5), (6), (7)
use the existing TractX source restoration and its original-graph machines.
The two EO clauses and matching consume Gamma directly. In particular,
single-weight's BothChargeSigns is not assumed to survive restriction to G.
All seven have the SAME validated graph encoding, original G/equality
coefficient presentation and original value, including zero/nullary labels.

Choice installs one already constructed machine for the fixed family. It
does not classify varying families, select a runtime point, or assert Hard.
The fixed-range entry is a specialization of this sole machine constructor.
All operational and resource observations below concern that same Computes.
-/
namespace Holant.LocalDrafts.MainChain.ReturnedLPTractSourceV2
open Turing Computability Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines
noncomputable section

namespace Raw
export Holant.LocalDrafts.RemoteWork.RationalLP.RawSource (RunsOn)
end Raw

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev signatureSet := Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet G
abbrev Input := {r : RawClosedNetwork // r.WellFormed s 1 arity}
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 arity
abbrev presentation := OriginalFamily.presentation G KSourceTransport.equalityEdges
abbrev value := OriginalFamily.value G KSourceTransport.equalityEdges

/-- The original indexed labels, with their original arities and entries. -/
theorem original_member (i : Fin s) :
    (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ signatureSet G := ⟨i,rfl⟩

/-- Finiteness is derived from the indexed range, including the empty family. -/
theorem original_finite : (signatureSet G).Finite := Set.finite_range _

/-- Every literal original label is in Gamma by the supplied original
membership. No transform or preprocessing changes this indexed range. -/
theorem original_subset (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀i,(⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma) :
    signatureSet G ⊆ Gamma := by
  rintro _ ⟨i,rfl⟩
  exact hmem i

private theorem original_machine_exists (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀i,(⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (h : Tract Gamma) :
    Nonempty (Computes (inputEncoding (s:=s) (arity:=arity))
      (presentation G).encoding (value G)) := by
  have hpre : preprocess (signatureSet G) ⊆ preprocess Gamma :=
    preprocess_mono (original_subset G Gamma hmem)
  have hFpre : (preprocess (signatureSet G)).Finite :=
    (original_finite G).subset (fun _ hf => hf.1)
  rcases h.2 with ho | hs | ht | hm | ha | hp | hl
  · exact ⟨ReturnedLPOneSidedSource.computes G Gamma hmem ho⟩
  · exact ⟨ReturnedLPSingleWeightSource.computes G Gamma hmem hs⟩
  · have htF : ArityTwoAlternative (preprocess (signatureSet G)) :=
      fun f hf => ht f (hpre hf)
    exact ⟨TractXCoreSource.sourceEqualityComputes G (signatureSet G)
      (original_member G) (original_finite G) ⟨hFpre,Or.inl htF⟩⟩
  · exact ⟨TractCoreSource.matchingComputes G Gamma hmem hm⟩
  · exact ⟨TractXCoreSource.sourceEqualityComputes G (signatureSet G)
      (original_member G) (original_finite G)
      ⟨hFpre,Or.inr (Or.inl (ha.mono_family hpre))⟩⟩
  · exact ⟨TractXCoreSource.sourceEqualityComputes G (signatureSet G)
      (original_member G) (original_finite G)
      ⟨hFpre,Or.inr (Or.inr (Or.inl (hp.mono_family hpre)))⟩⟩
  · exact ⟨TractXCoreSource.sourceEqualityComputes G (signatureSet G)
      (original_member G) (original_finite G)
      ⟨hFpre,Or.inr (Or.inr (Or.inr (hl.mono_family hpre)))⟩⟩

/-- SOLE machine constructor. The original Gamma criterion selects its
actual clause before restriction; no Tract(subfamily) promise is requested. -/
def computesOfFamily (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀i,(⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (h : Tract Gamma) :
    Computes (inputEncoding (s:=s) (arity:=arity)) (presentation G).encoding (value G) :=
  Classical.choice (original_machine_exists G Gamma hmem h)

theorem inFPOfFamily (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀i,(⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (h : Tract Gamma) :
    InFP (inputEncoding (s:=s) (arity:=arity)) (presentation G).encoding (value G) :=
  (computesOfFamily G Gamma hmem h).inFP

variable (h : Tract (signatureSet G))

/-- Fixed-range specialization of the sole original-family constructor.
Its runtime input and original answer encoding are unchanged. -/
def computes : Computes (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) :=
  computesOfFamily G (signatureSet G) (original_member G) h

include h in
theorem inFP : InFP (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) := (computes G h).inFP

/-- The answer is the original ordered equality-wire contraction. Loops,
parallel incidences, zero tensors and nullary factors stay in this network. -/
theorem answer_ambient (r : Input (s:=s) (arity:=arity)) :
    (value G r : AlgebraicComplex)=
      (r.val.realize r.property G KSourceTransport.equalityEdges).denote Fin.elim0 :=
  OriginalFamily.value_exact G KSourceTransport.equalityEdges r

def timePolynomial : Polynomial ℕ := (computes G h).time
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial (computes G h)
def storagePolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial G h

theorem clock : timePolynomial G h=(computes G h).time := rfl

/-- Same programme, same input bytes, same original coefficient answer. -/
def actual_output (r : Input (s:=s) (arity:=arity)) :
    TM2OutputsInTime (computes G h).machine.computer (inputEncoding.encode r)
      (some ((presentation G).encoding.encode (value G r)))
      ((timePolynomial G h).eval (inputEncoding.encode r).length) :=
  (computes G h).outputs r

theorem execution (r : Input (s:=s) (arity:=arity)) :
    Raw.RunsOn (computes G h).machine.computer.step
      (initList (computes G h).machine.computer (inputEncoding.encode r))
      (haltList (computes G h).machine.computer ((presentation G).encoding.encode (value G r)))
      ((computes G h).outputs r).steps := ((computes G h).outputs r).evals_in_steps

theorem steps_bound (r : Input (s:=s) (arity:=arity)) :
    ((computes G h).outputs r).steps ≤
      (timePolynomial G h).eval (inputEncoding.encode r).length :=
  ((computes G h).outputs r).steps_le_m

theorem primitive_bound (r : Input (s:=s) (arity:=arity)) :
    primitiveCost (computes G h).machine ((computes G h).outputs r).steps
      (some (initList (computes G h).machine.computer (inputEncoding.encode r))) ≤
      (primitivePolynomial G h).eval (inputEncoding.encode r).length :=
  computes_primitive_cost (computes G h) r

theorem output_bits (r : Input (s:=s) (arity:=arity)) :
    ((presentation G).encoding.encode (value G r)).length ≤
      (computes G h).outputBound.bound.eval (inputEncoding.encode r).length :=
  (computes G h).outputBound.length_le r

/-- Abstract only the receipt in this proof. The installed programme is not
unfolded or replaced, and no separate storage hypothesis is introduced. -/
private theorem computes_prefix_size {α β : Type} {ea : Encoding α Bool}
    {eb : Encoding β Bool} {f : α → β} (M : Computes ea eb f) (a : α) (i : ℕ)
    (hi : i ≤ M.time.eval (ea.encode a).length) (cfg : M.machine.Config)
    (hc : Raw.RunsOn M.machine.computer.step
      (initList M.machine.computer (ea.encode a)) cfg i) :
    stackSize cfg.stk ≤
      (Polynomial.X+FixedFieldMachines.primitivePolynomial M).eval (ea.encode a).length := by
  have hs := M.machine.run_size_le _ cfg i hc
  rw [Machine.size_init] at hs
  have hb := Nat.mul_le_mul_right M.machine.primitiveBudget hi
  apply hs.trans
  simpa only [FixedFieldMachines.primitivePolynomial,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left hb (ea.encode a).length

/-- Every actual prefix within this same installed clock includes all
branch-internal parser, LP, completion, transport and cleanup stacks. -/
theorem temporary_bits (r : Input (s:=s) (arity:=arity)) (i : ℕ)
    (hi : i ≤ (timePolynomial G h).eval (inputEncoding.encode r).length)
    (cfg : (computes G h).machine.Config)
    (hc : Raw.RunsOn (computes G h).machine.computer.step
      (initList (computes G h).machine.computer (inputEncoding.encode r)) cfg i) :
    stackSize cfg.stk ≤ (storagePolynomial G h).eval (inputEncoding.encode r).length := by
  simpa only [storagePolynomial,primitivePolynomial] using
    computes_prefix_size (computes G h) r i hi cfg hc

end
end Holant.LocalDrafts.MainChain.ReturnedLPTractSourceV2
