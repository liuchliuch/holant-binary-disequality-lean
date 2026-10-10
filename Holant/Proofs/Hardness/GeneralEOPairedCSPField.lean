import Holant.Proofs.Hardness.GeneralEOPairedCSPTotal
import Holant.Complexity.FixedGadgetSubstitution.OriginalFamily

/-! Original finite-family algebraic coefficients internally determine the
single field and faithful answer codec used throughout the native programme.
No larger field, substitute oracle family, or coefficient certificate is input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {L : Type} [Field L] [Algebra ℚ L] {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature L (arity i.val))

def coefficient : ExactSignatureTables.CoefficientIndex s 1 arity→L
  | .inl ⟨i,x⟩ => G i x
  | .inr (_,a,b) => Signature.disequality a b

theorem coefficient_algebraic (halg : ∀i x,IsAlgebraic ℚ (G i x)) :
    ∀c,IsAlgebraic ℚ (coefficient G c) := by
  intro c
  cases c with
  | inl c => exact halg c.1 c.2
  | inr c =>
    rcases c with ⟨i,a,b⟩
    cases a <;> cases b <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

abbrev field := familyField (coefficient G)
local instance fieldAlgebra : Algebra ℚ (field G) := (field G).algebra'
abbrev presentation (halg : ∀i x,IsAlgebraic ℚ (G i x)) :=
  familyPresentation (coefficient G) (coefficient_algebraic G halg)

def signatures (i : Fin s) : Signature (field G) (arity i.val) :=
  fun x=>fieldCoefficient (coefficient G) (.inl ⟨i,x⟩)

@[simp] theorem signature_value (i : Fin s) (x : Fin (arity i.val)→Bool) :
    ((signatures G i x : field G) : L)=G i x := rfl

theorem covers (label : Fin s) (p : OrientedPerfectPairing (arity label.val))
    (hf : GeneralEOPairedCSPCycles.Covers p (G label)) :
    GeneralEOPairedCSPCycles.Covers p (signatures G label) := by
  intro x hx
  apply hf x
  intro hh
  apply hx
  apply Subtype.ext
  exact hh

def sourceValue (label : Fin s) (p : OrientedPerfectPairing (arity label.val))
    (r : GeneralEOPairedCSPRaw.Input p.count) : field G :=
  GeneralEOPairedCSPNative.sourceValue (signatures G) label p r

def targetValue (halg : ∀i x,IsAlgebraic ℚ (G i x)) :
    GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity)→field G :=
  GeneralEOPairedCSPNative.targetValue (presentation G halg) (signatures G)

theorem source_value_exact (label : Fin s) (p : OrientedPerfectPairing (arity label.val))
    (r : GeneralEOPairedCSPRaw.Input p.count) :
    ((sourceValue G label p r : field G) : L)=
      GeneralEOPairedCSPRaw.value p (GeneralEOPairedCSPCycles.compress p (G label)) r.val := by
  change (field G).subtype (GeneralEOPairedCSPRaw.value p
    (GeneralEOPairedCSPCycles.compress p (signatures G label)) r.val)=_
  simp only [GeneralEOPairedCSPRaw.value,GeneralEOPairedCSPCycles.compress,map_sum,map_prod]
  rfl

theorem target_value_exact (halg : ∀i x,IsAlgebraic ℚ (G i x))
    (r : GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity)) :
    ((targetValue G halg r : field G) : L)=
      (r.val.realize r.property G (fun _=>Signature.disequality)).denote Fin.elim0 := by
  rw [targetValue,GeneralEOPairedCSPNative.target_semantics]
  change (field G).subtype _=_
  rw [←Network.denote_map (field G).subtype]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    rfl
  · intro e a b
    cases a <;> cases b <;> rfl

theorem total_source_value_exact (label : Fin s) (p : OrientedPerfectPairing (arity label.val))
    (r : GeneralEOPairedCSPRaw.Raw) :
    ((GeneralEOPairedCSPTotal.value (signatures G) label p r : field G) : L)=
      GeneralEOPairedCSPTotal.value G label p r := by
  by_cases hr : r.WellFormed p.count
  · simp only [GeneralEOPairedCSPTotal.value,ite_eq_left hr]
    exact source_value_exact G label p ⟨r,hr⟩
  · simp only [GeneralEOPairedCSPTotal.value,ite_eq_right hr]
    rfl

/-- The controlled reduction uses the field and codec derived from precisely
all original family entries and X; the retained original label stays explicit. -/
def controlled (halg : ∀i x,IsAlgebraic ℚ (G i x)) (label : Fin s)
    (p : OrientedPerfectPairing (arity label.val))
    (hf : GeneralEOPairedCSPCycles.Covers p (G label)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPRaw.inputEncoding p.count)
      (presentation G halg).encoding (RawClosedNetwork.validatedEncoding s 1 arity)
      (presentation G halg).encoding (sourceValue G label p) (targetValue G halg) :=
  GeneralEOPairedCSPNative.controlled (presentation G halg) (signatures G) label p
    (covers G label p hf)

/-- The total version physically rejects malformed raw records before querying
and uses the identical original-field answer codec. -/
def totalControlled (halg : ∀i x,IsAlgebraic ℚ (G i x)) (label : Fin s)
    (p : OrientedPerfectPairing (arity label.val))
    (hf : GeneralEOPairedCSPCycles.Covers p (G label)) :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding
      (presentation G halg).encoding (RawClosedNetwork.validatedEncoding s 1 arity)
      (presentation G halg).encoding
      (GeneralEOPairedCSPTotal.value (signatures G) label p) (targetValue G halg) :=
  GeneralEOPairedCSPTotal.controlled (presentation G halg) (signatures G) label p
    (covers G label p hf)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPField
