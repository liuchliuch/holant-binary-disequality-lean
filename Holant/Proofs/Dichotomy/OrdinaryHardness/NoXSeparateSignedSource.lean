import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedProjection

/-! Original-table, pin-only realization of a separate signed-bundle resource.
Both signs keep their own proved incidence counts; every emitted label is
literal. The coefficient on opposite assignments is the unchanged source row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXSeparateSignedSource
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSignedPortsCore (Port word)
namespace P
export NoXSeparateSignedProjection (arity table recipe signedCount constant_count positive_count negative_count opposite_value)
end P
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe coefficient_eq ports_eq)
end R
namespace U
export OrdinaryNegativeXUniversalResource (OddResource)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s m : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (ps : Fin (b j.val)→Port m)

def labels : Fin 3→Fin s := ![j,p0,p1]

include h0 h1 in
theorem literal (i : Fin 3) :
    (⟨b (labels j p0 p1 i).val,H (labels j p0 p1 i)⟩ : AnySignature K)=
      ⟨P.arity (b j.val) i.val,P.table (H j) i⟩ := by
  fin_cases i
  · rfl
  · exact h0
  · exact h1

def rows : Recipe (u:=1) (s:=s) (a:=fun _=>m+m) (b:=b) :=
  R.exactRecipe (labels j p0 p1) (P.table (H j)) H (literal H j p0 p1 h0 h1) (P.recipe ps)

theorem ports_exact (i : Fin 1) : ports (rows H j p0 p1 h0 h1 ps) i=ports (P.recipe ps) i :=
  R.ports_eq _ _ _ i

variable (odd : ∀q bit,Odd (P.signedCount ps q bit))

def resource : U.OddResource (s:=s) b (m+m) where
  privateCount := 0
  rows := rows H j p0 p1 h0 h1 ps
  constant_even bit := by
    rw [ports_exact,P.constant_count]
    exact Even.mul_right (by decide : Even 2) _
  boundary_odd q := by
    change Odd ((ports (rows H j p0 p1 h0 h1 ps) 0).count (.inr q))
    rw [ports_exact]
    refine Fin.addCases ?_ ?_ q
    · intro i
      rw [P.positive_count]
      exact odd i false
    · intro i
      rw [P.negative_count]
      exact odd i true
  private_even i := Fin.elim0 i

theorem value (z : Fin m→Bool) :
    (resource H j p0 p1 h0 h1 ps odd).signature H (Fin.addCases z (fun i=>!(z i)))=H j (word ps z) := by
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>m+m) H 0 (rows H j p0 p1 h0 h1 ps) 0 _=_
  rw [OrdinaryNegativeSparseMixingSource.trace_zero]
  rw [rows,R.coefficient_eq,P.opposite_value]

theorem ambient_value (z : Fin m→Bool) :
    (resource H j p0 p1 h0 h1 ps odd).ambient H (Fin.addCases z (fun i=>!(z i)))=
      (H j (word ps z) : AlgebraicComplex) := by
  change ((resource H j p0 p1 h0 h1 ps odd).signature H _ : AlgebraicComplex)=_
  rw [value]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXSeparateSignedSource
end
