import Holant.Proofs.Hardness.GeneralEOPairedFamilyPrivateValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilyMinorSource

/-! Actual mixed-family marginal source. Validation sends malformed records
to a fixed malformed target; every accepted query retains labels and allocates
exactly one disjoint k-bit block per row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyPrivateSource
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler GeneralEOPairedCSPFamilyRaw
namespace W
export GeneralEOPairedFamilyPrivateRaw (query queryComputes)
export GeneralEOPairedFamilyPrivateValue (trace query_valid query_value)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a b : ℕ → ℕ}
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (b i.val))
variable (k : ℕ) (hcount : ∀i,(P i).count=(Q i).count+k)

def rejected : Raw s := ⟨0,[],[0]⟩

theorem rejected_invalid : ¬(rejected (s:=s)).WellFormed P := by
  intro h
  have hh := h.1
  simp [rejected,Raw.edgeCount] at hh

def validatedQuery (r : Raw s) : Raw s :=
  if r.WellFormed Q then W.query Q P k hcount r else rejected

def validatedComputes : Computes (encoding s) (encoding s) (validatedQuery Q P k hcount) :=
  congrComputes (ifComputes (GeneralEOPairedCSPFamilyValidation.validates Q)
    (W.queryComputes Q P k hcount) (constantComputes (encoding s) (encoding s) rejected))
    (fun r=>by simp [validatedQuery])

variable {K : Type} [CommSemiring K]

def total (g : (i : Fin s) → Signature K (P i).count) (r : Raw s) : K :=
  if r.WellFormed P then value P g r else 0

def marginalValue (g : (i : Fin s) → Signature K (P i).count) : Raw s → K :=
  total Q (W.trace Q P k hcount g)

theorem query_value (g : (i : Fin s) → Signature K (P i).count) (r : Raw s) :
    marginalValue Q P k hcount g r=total P g (validatedQuery Q P k hcount r) := by
  by_cases hr : r.WellFormed Q
  · simp only [marginalValue,total,validatedQuery,ite_eq_left hr,
      ite_eq_left (W.query_valid Q P k hcount r hr)]
    exact (W.query_value Q P k hcount g r hr).symm
  · simp only [marginalValue,total,validatedQuery,ite_eq_right hr,
      ite_eq_right (rejected_invalid P)]

/-- The only bound parameter is a concrete bound for the already specified
target value. The query writer and all weighted equalities are constructed here. -/
def controlled (g : (i : Fin s) → Signature K (P i).count) (e : Encoding K Bool)
    (hb : PolynomialOutputBound (encoding s) e (total P g)) :
    LengthControlledOracleReduction (encoding s) e (encoding s) e
      (marginalValue Q P k hcount g) (total P g) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (validatedComputes Q P k hcount)
    (identityComputes e) hb (marginalValue Q P k hcount g) (query_value Q P k hcount g)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyPrivateSource
