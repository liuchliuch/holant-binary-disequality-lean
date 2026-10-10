import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiOppositeCap

/-! Two actual copies of any full odd-interface unary and one actual weighted
antidiagonal produce an even non-Affine unary when the fourth powers differ.
Heterogeneous private expansion is literal and preserves every original label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedOddUnaryCap
open Holant Holant.Tractable
open scoped BigOperators
open OrdinaryNegativeMixedBlockData
namespace U
export OrdinaryNegativeXUniversalResource (OddResource EvenBad)
end U
namespace P
export OrdinaryNegativeXUniversalPair (arity table block block_value)
end P
namespace A
export NoXWeightedAntiSigned (anti)
export NoXWeightedAntiOppositeCap (antiResource anti_ambient)
end A
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def outer : Recipe (u:=1) (s:=2) (a:=fun _=>1+1) (b:=P.arity 1 2) :=
  fun _=>[⟨1,![.inr (0 : Fin 2),.inr (1 : Fin 2)]⟩,
    ⟨0,fun _=>.inr (0 : Fin 2)⟩,⟨0,fun _=>.inr (1 : Fin 2)⟩]

theorem outer_even : EvenRecipe outer := by
  intro i q
  fin_cases i
  cases q with
  | inl b => cases b <;> decide
  | inr j => fin_cases j <;> decide

variable {K : Type} [Field K]

theorem coefficient_value (f : Signature K 1) (v w : K) (bits : Fin 2→Bool) :
    coefficient (P.table f (A.anti v w)) outer 0 bits=
      A.anti v w ![bits 0,bits 1]*f (fun _=>bits 0)*f (fun _=>bits 1) := by
  change A.anti v w ![bits 0,bits 1]*(f (fun _=>bits 0)*(f (fun _=>bits 1)*1))=_
  ring

theorem trace_value (f : Signature K 1) (v w : K) (z : Fin 1→Bool) :
    M.trace (P.table f (A.anti v w)) 1 outer 0 z=
      f (fun _=>false)*f (fun _=>true)*(if z 0 then w else v) := by
  unfold M.trace
  simp_rw [coefficient_value]
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  change (∑q : Bool,A.anti v w ![z 0,q]*f (fun _=>z 0)*f (fun _=>q))=_
  cases z 0 <;> simp [A.anti,mul_comm,mul_left_comm]

section Actual
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (antiLabel : Fin s)
variable (v w : K)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,A.anti v w⟩)
variable (resource : U.OddResource (s:=s) b 1)

def block : OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b) 1 :=
  P.block (n:=1) (m:=2) (d:=1) (l:=1) resource (A.antiResource H antiLabel v w ha_lit) outer outer_even

theorem anti_signature : (A.antiResource H antiLabel v w ha_lit).signature H=A.anti v w := by
  funext z
  apply Subtype.ext
  have h := congrFun (A.anti_ambient H antiLabel v w ha_lit) z
  calc
    _=A.anti (v : AlgebraicComplex) (w : AlgebraicComplex) z := h
    _=_ := by
      cases hz0 : z 0 <;> cases hz1 : z 1 <;> simp [A.anti,hz0,hz1]

theorem block_value (z : Fin 1→Bool) :
    (block H antiLabel v w ha_lit resource).signature H z=
      resource.signature H (fun _=>false)*resource.signature H (fun _=>true)*(if z 0 then w else v) := by
  rw [block,P.block_value,anti_signature,trace_value]

variable (hv : v≠0) (hw : w≠0)
variable (full : ∀z,resource.ambient H z≠0)
variable (fourth : (v : AlgebraicComplex)^4≠(w : AlgebraicComplex)^4)

include ha_lit hv hw full fourth in
theorem evenBad : U.EvenBad H := by
  refine ⟨1,block H antiLabel v w ha_lit resource,?_⟩
  intro affine
  have hn (z : Fin 1→Bool) :
      ((block H antiLabel v w ha_lit resource).signature H z : AlgebraicComplex)≠0 := by
    rw [block_value]
    change (resource.ambient H (fun _=>false)*resource.ambient H (fun _=>true))*
      ((if z 0 then w else v : K) : AlgebraicComplex)≠0
    apply mul_ne_zero (mul_ne_zero (full _) (full _))
    cases z 0
    · exact fun h=>hv (Subtype.ext h)
    · exact fun h=>hw (Subtype.ext h)
  have he := affine.fourth_power_eq (fun _=>false) (fun _=>true) (hn _) (hn _)
  simp only [block_value,Bool.false_eq_true,ite_false,ite_true,IntermediateField.coe_mul,mul_pow] at he
  exact fourth (mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 (full (fun _=>false)))
    (pow_ne_zero 4 (full (fun _=>true)))) he)
end Actual

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedOddUnaryCap
end
