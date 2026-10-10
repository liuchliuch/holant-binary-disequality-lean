import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOnePins
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneMarginal

/-! One odd orientation and one even orientation yield an actual unary odd
resource by summing the even orientation. All original pinning is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneOdd
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace P
export NoXSeparateSignedProjection (signedCount constant_count positive_count negative_count coefficient_value)
export OrdinaryNegativeSignedRowsPins (signedCompose)
end P
namespace S
export NoXSeparateSignedSource (rows ports_exact)
export NoXSeparateSignedPins (signedCount_compose)
end S
namespace R
export NoXReciprocalSelectionRankOne (ports projected)
export NoXReciprocalSelectionRankOnePins (minor separated_compose)
end R
namespace M
export NoXReciprocalSelectionRankOneMarginal (scale scale_ne_zero value)
end M
namespace U
export OrdinaryNegativeXUniversalResource (OddResource)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s n : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin n) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (x y : Fin n→Bool)
variable (odd : Odd (P.signedCount (R.ports x y) 0 false))
variable (even : Even (P.signedCount (R.ports x y) 0 true))
def rows := S.rows H j p0 p1 h0 h1 (P.signedCompose pins (R.ports x y))
def resource : U.OddResource (s:=s) b 1 where
  privateCount := 1
  rows := rows H j p0 p1 h0 h1 pins x y
  constant_even bit := by
    rw [rows,S.ports_exact,P.constant_count]
    exact Even.mul_right (by decide : Even 2) _
  boundary_odd i := by
    have hi:i=0 := Fin.eq_zero i
    subst i
    change Odd ((ports (rows H j p0 p1 h0 h1 pins x y) 0).count (.inr (Fin.castAdd 1 (0 : Fin 1))))
    rw [rows,S.ports_exact,P.positive_count,S.signedCount_compose pins pure]
    exact odd
  private_even i := by
    have hi:i=0 := Fin.eq_zero i
    subst i
    change Even ((ports (rows H j p0 p1 h0 h1 pins x y) 0).count (.inr (Fin.natAdd 1 (0 : Fin 1))))
    rw [rows,S.ports_exact,P.negative_count,S.signedCount_compose pins pure]
    exact even

variable (support : ∀z,R.minor H j pins z≠0→z=x ∨ z=y)
include support in
theorem value (z : Fin 1→Bool) :
    (resource H j p0 p1 h0 h1 pins pure x y odd even).signature H z=
    M.scale (K:=K) x y*(if z 0 then R.minor H j pins y else R.minor H j pins x) := by
  obtain ⟨positive,hp⟩ := NoXReciprocalSelectionRankOneSource.signed_live (R.ports x y) 0 false odd
  have pos:x positive=false ∧ y positive=true := by
    cases hx:x positive <;> cases hy:y positive <;> simp [R.ports,hx,hy] at hp ⊢
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>1) H 1 (rows H j p0 p1 h0 h1 pins x y) 0 z=_
  unfold OrdinaryNegativeMixedBlockSource.trace
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  change (∑v : Bool,coefficient H (rows H j p0 p1 h0 h1 pins x y) 0 (Fin.addCases z (fun _=>v)))=_
  have coeff (v : Bool) : coefficient H (rows H j p0 p1 h0 h1 pins x y) 0
      (Fin.addCases z (fun _=>v))=R.projected (R.minor H j pins) x y ![z 0,v] := by
    rw [rows,S.rows,OrdinaryNegativeMixedBlockRelabel.coefficient_eq,P.coefficient_value,R.separated_compose]
    have eqn : (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>Bool) z (fun _=>v) : Fin 2→Bool)=![z 0,v] := by
      funext i;fin_cases i <;> rfl
    rw [eqn]
    rfl
  simp_rw [coeff]
  exact M.value x y (R.minor H j pins) support positive pos (z 0)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOneOdd
end
