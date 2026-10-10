import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOne

/-! A two-point original support with odd counts in both orientations has
an actual unsigned odd-boundary anti recipe. No X label occurs in its rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneSource
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port)
namespace P
export NoXSeparateSignedProjection (signedCount coefficient_value)
end P
namespace S
export NoXSeparateSignedSource (resource rows)
end S
namespace R
export NoXReciprocalSelectionRankOne (ports projected anti)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false

theorem signed_live {n m : ℕ} (ps : Fin n→Port m) (q : Fin m) (bit : Bool)
    (odd : Odd (P.signedCount ps q bit)) : ∃i,ps i=.inr (q,bit) := by
  classical
  by_contra none
  have each : ∀i,ps i≠.inr (q,bit) := by simpa only [not_exists] using none
  have zero : P.signedCount ps q bit=0 := by simp [P.signedCount,each]
  rw [zero] at odd
  simpa using odd

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (x y : Fin (b j.val)→Bool)
variable (odd : ∀q bit,Odd (P.signedCount (R.ports x y) q bit))

def resource := S.resource H j p0 p1 h0 h1 (R.ports x y) odd

theorem value (z : Fin 2→Bool) :
    (resource H j p0 p1 h0 h1 x y odd).signature H z=R.projected (H j) x y z := by
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>2) H 0 (S.rows H j p0 p1 h0 h1 (R.ports x y)) 0 z=_
  rw [OrdinaryNegativeSparseMixingSource.trace_zero,S.rows,
    OrdinaryNegativeMixedBlockRelabel.coefficient_eq,P.coefficient_value]
  rfl

variable (support : ∀z,H j z≠0→z=x ∨ z=y)
include support in
theorem anti : (resource H j p0 p1 h0 h1 x y odd).signature H=
    NoXWeightedAntiSigned.anti (H j x) (H j y) := by
  obtain ⟨positive,hp⟩ := signed_live (R.ports x y) 0 false (odd 0 false)
  obtain ⟨negative,hn⟩ := signed_live (R.ports x y) 0 true (odd 0 true)
  have pos : x positive=false ∧ y positive=true := by
    cases hx:x positive <;> cases hy:y positive <;> simp [R.ports,hx,hy] at hp ⊢
  have neg : x negative=true ∧ y negative=false := by
    cases hx:x negative <;> cases hy:y negative <;> simp [R.ports,hx,hy] at hn ⊢
  exact (funext (value H j p0 p1 h0 h1 x y odd)).trans
    (R.anti (H j) x y support positive negative pos neg)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneSource
end
