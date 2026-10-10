import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedPins

/-! Pure pinnings preserve the unsigned two-boundary anti resource and its
separate odd incidence. The zero diagonal follows from the actual minor's
support, not from an assumed flip operation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOnePins
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port)
namespace R
export NoXReciprocalSelectionRankOne (ports projected anti)
end R
namespace C
export NoXReciprocalSelectionRankOneSource (signed_live)
end C
namespace P
export NoXSeparateSignedProjection (rowPort signedCount coefficient_value)
export OrdinaryNegativeSignedRowsPins (signedCompose)
end P
namespace S
export NoXSeparateSignedPins (resource)
end S
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false

theorem separated_compose {N n m : ℕ} (pins : Fin N→Bool ⊕ Fin n)
    (ps : Fin n→Port m) (z : Fin (m+m)→Bool) :
    T.substitute (P.rowPort (P.signedCompose pins ps)) z=
    T.substitute pins (T.substitute (P.rowPort ps) z) := by
  funext i
  cases hi:pins i with
  | inl bit=>simp [T.substitute,P.rowPort,P.signedCompose,hi]
  | inr q=>
    cases hq:ps q with
    | inl bit=>simp [T.substitute,P.rowPort,P.signedCompose,hi,hq]
    | inr v=>rcases v with ⟨j,bit⟩;cases bit <;> simp [T.substitute,P.rowPort,P.signedCompose,hi,hq]

variable {K : IntermediateField ℚ AlgebraicComplex} {s n : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin n) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (x y : Fin n→Bool)
variable (odd : ∀q bit,Odd (P.signedCount (R.ports x y) q bit))
abbrev minor : Signature K n := fun z=>H j (T.substitute pins z)
def resource := S.resource (R.ports x y) H j p0 p1 h0 h1 pins pure odd

theorem value (z : Fin 2→Bool) :
    (resource H j p0 p1 h0 h1 pins pure x y odd).signature H z=R.projected (minor H j pins) x y z := by
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>2) H 0
    (NoXSeparateSignedSource.rows H j p0 p1 h0 h1 (P.signedCompose pins (R.ports x y))) 0 z=_
  rw [OrdinaryNegativeSparseMixingSource.trace_zero,NoXSeparateSignedSource.rows,
    OrdinaryNegativeMixedBlockRelabel.coefficient_eq,P.coefficient_value,separated_compose]
  rfl

variable (support : ∀z,minor H j pins z≠0→z=x ∨ z=y)
include support in
theorem anti : (resource H j p0 p1 h0 h1 pins pure x y odd).signature H=
    NoXWeightedAntiSigned.anti (minor H j pins x) (minor H j pins y) := by
  obtain ⟨positive,hp⟩ := C.signed_live (R.ports x y) 0 false (odd 0 false)
  obtain ⟨negative,hn⟩ := C.signed_live (R.ports x y) 0 true (odd 0 true)
  have pos : x positive=false ∧ y positive=true := by
    cases hx:x positive <;> cases hy:y positive <;> simp [R.ports,hx,hy] at hp ⊢
  have neg : x negative=true ∧ y negative=false := by
    cases hx:x negative <;> cases hy:y negative <;> simp [R.ports,hx,hy] at hn ⊢
  exact (funext (value H j p0 p1 h0 h1 pins pure x y odd)).trans
    (R.anti (minor H j pins) x y support positive negative pos neg)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOnePins
end
