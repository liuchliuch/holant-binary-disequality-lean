import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPinProgramme
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyNative

/-! The actual reserved-pin programme over any fixed coefficient field.
This permits finite duplicate palettes with reoriented covering pairings
without changing the answer field or introducing a supplied pin source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinNative
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose
namespace R
export GeneralEOPairedFamilyExtractionPinRaw
  (free merge augment fixed free_merge_wellFormed free_augment_wellFormed)
end R
namespace V
export GeneralEOPairedFamilyExtractionPinValue (SelfDual recover_selfdual recover_distinguished)
end V
namespace Q
export GeneralEOPairedFamilyExtractionPinProgramme
  (witness witness_unequal two four validQueries queries pre post postValue post_empty query_count)
end Q
namespace N
export GeneralEOPairedCSPFamilyNative (totalValue totalControlled)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d)
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

def coefficients (i : Fin s) :=
  GeneralEOPairedCSPCycles.compress (P i) (G i)

/-- A source record declares free variables only. References 0,1 mean fixed
false,true; free variable k is addressed by k+2. Malformed records return zero. -/
def value (r : GeneralEOPairedCSPFamilyRaw.Raw s) : K :=
  if (R.free r).WellFormed P then R.fixed P (coefficients G P) r false true else 0

omit [Algebra ℚ K] [CharZero K] in
theorem valid_value (q : GeneralEOPairedCSPFamilyRaw.Raw s) (hq : q.WellFormed P) :
    N.totalValue G P q=GeneralEOPairedCSPFamilyRaw.value P (coefficients G P) q :=
  ite_eq_left hq

omit [Algebra ℚ K] in
theorem post_correct (r : GeneralEOPairedCSPFamilyRaw.Raw s) :
    value G P r=Q.postValue P (coefficients G P)
      (OracleBatch.answers (N.totalValue G P) (Q.queries P (coefficients G P) r,false)) := by
  by_cases hr : (R.free r).WellFormed P
  · have hm := R.free_merge_wellFormed P r hr
    by_cases hs : V.SelfDual P (coefficients G P)
    · simp only [value, ite_eq_left hr, Q.queries, Q.validQueries, dite_eq_left hs,
        Q.two, OracleBatch.answers, List.map_cons, List.map_nil,
        Q.postValue, List.getD_cons_zero, List.getD_cons_succ,
        valid_value G P _ hr, valid_value G P _ hm]
      exact V.recover_selfdual P (coefficients G P) hs r hr
    · let w := Q.witness P (coefficients G P) hs
      have hw := R.free_augment_wellFormed P w.1 w.2 r hr
      have hwm := R.free_merge_wellFormed P (R.augment P w.1 w.2 r) hw
      simp only [value, ite_eq_left hr, Q.queries, Q.validQueries, dite_eq_right hs,
        Q.four, OracleBatch.answers, List.map_cons, List.map_nil,
        Q.postValue, List.getD_cons_zero, List.getD_cons_succ]
      change _=((N.totalValue G P (R.free (R.augment P w.1 w.2 r))-
        N.totalValue G P (R.merge (R.augment P w.1 w.2 r)))-
          coefficients G P w.1 (GeneralEOPairedFamilyExtractionPinValue.flip w.2)*
            (N.totalValue G P (R.free r)-N.totalValue G P (R.merge r)))/_
      rw [valid_value G P _ hr, valid_value G P _ hm,
        valid_value G P _ hw, valid_value G P _ hwm]
      exact V.recover_distinguished P (coefficients G P) w.1 w.2
        (Q.witness_unequal P (coefficients G P) hs) r
  · simp only [value, ite_eq_right hr, Q.queries, OracleBatch.answers, List.map_nil, Q.post_empty]

/-- No pin, no auxiliary signature, no chosen separating row and no hardness
backend is required. The target is the actual accepted raw compressed-family
oracle and its original-family working-field answer presentation. -/
def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding s) F.encoding
      (GeneralEOPairedCSPFamilyRaw.encoding s) F.encoding
      (value G P) (N.totalValue G P) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (Q.pre P (coefficients G P)) (Q.post P F (coefficients G P))
    (N.totalControlled F G P hf).sourceOutputBound
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho r
  rw [post_correct]
  exact reduction.reduction.correct oracle ho r


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinNative
