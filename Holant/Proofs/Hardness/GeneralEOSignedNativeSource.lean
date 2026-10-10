import Holant.Proofs.Hardness.GeneralEOSignedNativeProgram
import Holant.Proofs.Hardness.GeneralEOSignedNativeQueryValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilySignedOriginal

/-! Complete physical native-network to signed compressed-CSP reduction.
Both the actual signed query and its Good/unused context are computed from the
original raw bytes. The answer correction removes the exact double-cover
unused factor in one fixed field. The final composition uses the original
family's proved coordinate adapter and original oracle codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open scoped BigOperators
namespace R
export GeneralEOSignedNativeRaw (Input inputEncoding parsed parsedComputes)
end R
namespace Q
export GeneralEOSignedNativeQuery (count label signs query)
end Q
namespace Pr
export GeneralEOSignedNativeProgram (queryComputes)
end Pr
namespace D
export GeneralEOSignedNativeDecoded (nativeValue signedQueryValue normalizedValue normalized_eq)
end D
namespace U
export GeneralEOSignedParityUnused (contextEncoding context contextComputes normalize normalizeComputes unused_eq)
end U
namespace S
export GeneralEOPairedFamilySigned (value controlled)
end S
namespace F
export GeneralEOPairedCSPFamilyRaw (Raw encoding)
end F
namespace T
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end T
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d s : ℕ} {arity : ℕ → ℕ}
variable (Ff : FixedField K d) (G : (i : Fin s) → Signature K (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

def preprocessing (r : R.Input (s:=s) (arity:=arity)) : List (F.Raw (Q.count P)) × (Bool × ℕ) :=
  ([Q.query P r],U.context (R.parsed P r))

def pre : Computes (R.inputEncoding (s:=s) (arity:=arity))
    (OracleBatch.contextEncoding (F.encoding (Q.count P)) U.contextEncoding) (preprocessing P) :=
  pairComputes (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.list₁
    (F.encoding (Q.count P)) (Pr.queryComputes P)) ((R.parsedComputes P).andThen U.contextComputes)

def post : Computes (OracleBatch.contextEncoding Ff.encoding U.contextEncoding) Ff.encoding
    (fun a : List K × (Bool × ℕ) => U.normalize (a.1.getD 0 0,a.2)) :=
  (pairComputes
    ((Wiring.firstComputes (framedListEncoding Ff.encoding) U.contextEncoding).andThen
      (FixedGadgetSubstitution.Compiler.getDComputes Ff.encoding 0 0))
    (Wiring.secondComputes (framedListEncoding Ff.encoding) U.contextEncoding)).andThen
      (U.normalizeComputes Ff)

theorem normalization_correct (r : R.Input (s:=s) (arity:=arity))
    (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    U.normalize (D.signedQueryValue G P r,U.context (R.parsed P r))=D.nativeValue G r := by
  classical
  let net := r.val.realize r.property G (fun _ => Signature.disequality)
  let pairing := GeneralEOSignedNativeRaw.rowPairing P r
  have h := GeneralEOSignedParityUnused.normalize_eq (R.parsed P r)
    (GeneralEOSignedNativeParity.weight net.shape pairing net.vertex)
  have hs : (∑ y : Fin ((R.parsed P r).1*2) → Bool,
      GeneralEOSignedNativeParity.weight net.shape pairing net.vertex
        (GeneralEOSignedParityComponents.reconstruct (R.parsed P r).2 y)) =
      D.signedQueryValue G P r := by
    unfold D.signedQueryValue
    apply Finset.sum_congr rfl
    intro y _
    unfold GeneralEOSignedNativeParity.weight
    apply Finset.prod_congr rfl
    intro v _
    apply congrArg (GeneralEOPairedCSPCycles.compress (pairing v) (net.vertex v))
    exact GeneralEOSignedNativeParity.compressed_reconstruct net.shape pairing y v
  rw [hs] at h
  have hn := GeneralEOSignedNativeParity.denote_parity net pairing (fun _ => rfl)
    (fun v => hf (r.val.signatureLabel r.property v))
  exact h.trans hn.symm

theorem query_correct (r : R.Input (s:=s) (arity:=arity))
    (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    U.normalize (S.value G P (Q.label P) (Q.signs P) (Q.query P r),U.context (R.parsed P r))=
      D.nativeValue G r := by
  rw [GeneralEOSignedNativeQueryValue.value_eq]
  exact normalization_correct G P r hf

/-- One query on the actual signed palette, with a derived target-answer bound
and physical context-dependent correction. No CSP backend is a hypothesis. -/
def controlledToSigned (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (R.inputEncoding (s:=s) (arity:=arity)) Ff.encoding
      (F.encoding (Q.count P)) Ff.encoding (D.nativeValue G) (S.value G P (Q.label P) (Q.signs P)) := by
  let size := (S.controlled Ff G P (Q.label P) (Q.signs P) hf).sourceOutputBound
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch (pre P) (post Ff) size
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  rw [←query_correct G P r hf]
  simpa only [preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero]
    using reduction.reduction.correct oracle ho r

/-- The compiler and original-label signed realization are both actual
controlled machines, so their inlining preserves every physical obligation. -/
def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (R.inputEncoding (s:=s) (arity:=arity)) Ff.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) Ff.encoding
      (D.nativeValue G) (GeneralEOPairedCSPNative.targetValue Ff G) :=
  T.composeControlled (controlledToSigned Ff G P hf)
    (S.controlled Ff G P (Q.label P) (Q.signs P) hf)

section Original
namespace W
export GeneralEOPairedCSPField (field signatures covers)
end W
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
variable (H : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
local instance : Algebra ℚ (W.field H) := (W.field H).algebra'
local instance : CharZero (W.field H) := algebraRat.charZero (W.field H)

/-- The actual raw-network source ends at the unchanged original oracle and
its faithful original field-coordinate presentation. -/
def originalControlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (H i)) :
    LengthControlledOracleReduction (R.inputEncoding (s:=s) (arity:=arity)) (A.presentation H).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation H).encoding
      (D.nativeValue (W.signatures H)) (O.originalValue H) :=
  T.composeControlled (controlledToSigned (A.presentation H) (W.signatures H) P
      (fun i => W.covers H i (P i) (hf i)))
    (GeneralEOPairedFamilySignedOriginal.controlled H P (Q.label P) (Q.signs P) hf)
end Original
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeSource
