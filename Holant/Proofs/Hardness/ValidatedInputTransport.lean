import Holant.Proofs.Algorithms.TraceQueryControl

/-! Proof-only change of a validated domain. Input bits, machine, clock,
oracle endpoint and query bound are unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ValidatedInputTransport
open Computability Holant.Complexity
variable {α α' β γ δ : Type}
variable {ea : Encoding α Bool} {ea' : Encoding α' Bool} {eb : Encoding β Bool}
variable {ec : Encoding γ Bool} {ed : Encoding δ Bool}
variable {f : α→β} {f' : α'→β} {g : γ→δ}
def source (r : LengthControlledOracleReduction ea' eb ec ed f' g)
    (cast : α→α') (bytes : ∀ x,ea'.encode (cast x)=ea.encode x)
    (value : ∀ x,f' (cast x)=f x) : LengthControlledOracleReduction ea eb ec ed f g where
  reduction := {
    machine := r.reduction.machine
    time := r.reduction.time
    correct oracle ho x := by
      have h := r.reduction.correct oracle ho (cast x)
      rw [bytes,value] at h
      exact h }
  targetOutput := r.targetOutput
  queryBound := r.queryBound
  safeQuery oracle ho x t c hr hq := by
    have hr' := hr
    rw [←bytes x] at hr'
    have h := r.safeQuery oracle ho (cast x) t c hr' hq
    simpa only [bytes] using h
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ValidatedInputTransport
