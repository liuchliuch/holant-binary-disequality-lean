import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedSignedPorts
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Actual original-label signed resources for an arbitrary full weighted
antidiagonal. Odd/even incidence is literal; equal-fourth phase transport is
proved on the exact private sum rather than asserting a free X row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedSignedSource
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSignedPortsCore (Port word arity recipe external privatePort)
open scoped BigOperators
namespace W
export NoXWeightedSignedPorts (table trace trace_value weight portWeight weight_affine_iff)
end W
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe even_recipe coefficient_eq ports_eq)
end R
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize external_count private_count constant_count even_recipe)
end I
namespace U
export OrdinaryNegativeXUniversalResource (OddResource EvenBad)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s n m : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (f : Signature K n) (v w : K)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity n i.val,W.table f v w i⟩)
variable (p : Fin n→Port m)

def rows : Recipe (u:=1) (s:=s) (a:=fun _=>m+n) (b:=b) :=
  R.exactRecipe labels (W.table f v w) H literal (recipe p)

theorem ports_exact (i : Fin 1) : ports (rows H labels f v w literal p) i=ports (recipe p) i :=
  R.ports_eq _ _ _ i

def signature : Signature K m := OrdinaryNegativeMixedBlockSource.trace H n (rows H labels f v w literal p) 0

theorem value (z : Fin m→Bool) : signature H labels f v w literal p z=W.weight v w p z*f (word p z) := by
  unfold signature OrdinaryNegativeMixedBlockSource.trace rows
  simp_rw [R.coefficient_eq]
  exact W.trace_value f v w p z

theorem weight_coe (z : Fin m→Bool) :
    (W.weight (K:=K) v w p z : AlgebraicComplex)=W.weight (v : AlgebraicComplex) (w : AlgebraicComplex) p z := by
  change K.subtype (∏i,W.portWeight (K:=K) v w (p i) z)=
    ∏i,W.portWeight (v : AlgebraicComplex) (w : AlgebraicComplex) (p i) z
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases h : p i with
  | inl bit=>simp [W.portWeight]
  | inr pair=>
      rcases pair with ⟨j,sgn⟩
      cases sgn <;> cases hz : z j <;> simp [W.portWeight,hz] <;> rfl

theorem ambient_value (z : Fin m→Bool) :
    (signature H labels f v w literal p z : AlgebraicComplex)=
      W.weight (v : AlgebraicComplex) (w : AlgebraicComplex) p z*(f (word p z) : AlgebraicComplex) := by
  rw [value,IntermediateField.coe_mul]
  exact congrArg (fun c : AlgebraicComplex=>c*(f (word p z) : AlgebraicComplex)) (weight_coe v w p z)

def evenBlock (even : ∀j,Even (I.bundleSize p j)) : OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b) m where
  privateCount := n
  rows := rows H labels f v w literal p
  balanced := R.even_recipe labels (fun i=>congrArg Sigma.fst (literal i)) _ (I.even_recipe p even)

def oddResource (odd : ∀j,Odd (I.bundleSize p j)) : U.OddResource (s:=s) b m where
  privateCount := n
  rows := rows H labels f v w literal p
  constant_even bit := by
    rw [ports_exact,I.constant_count]
    exact Even.mul_right (by decide : Even 2) _
  boundary_odd j := by
    change Odd ((ports (rows H labels f v w literal p) 0).count (.inr (external j)))
    rw [ports_exact,I.external_count]
    exact odd j
  private_even i := by
    change Even ((ports (rows H labels f v w literal p) 0).count (.inr (privatePort i)))
    rw [ports_exact,I.private_count]
    decide

variable (hv : v≠0) (hw : w≠0) (fourth : (v : AlgebraicComplex)^4=(w : AlgebraicComplex)^4)
include hv hw fourth in
theorem affine_iff : Affine (fun z=>(signature H labels f v w literal p z : AlgebraicComplex)) ↔
    Affine (fun z=>(f (word p z) : AlgebraicComplex)) := by
  simp only [ambient_value]
  exact W.weight_affine_iff (v : AlgebraicComplex) (w : AlgebraicComplex)
    (fun h=>hv (Subtype.ext h)) (fun h=>hw (Subtype.ext h)) fourth p _

include hv hw fourth in
theorem alpha_iff :
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z=>(signature H labels f v w literal p z : AlgebraicComplex))) ↔
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z=>(f (word p z) : AlgebraicComplex))) := by
  have he : (OrdinaryNegativeOcticCommonBasis.basis true).symm.action
      (fun z=>(signature H labels f v w literal p z : AlgebraicComplex))=
      fun z=>W.weight (v : AlgebraicComplex) (w : AlgebraicComplex) p z*
        ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
          (fun z=>(f (word p z) : AlgebraicComplex))) z := by
    rw [OrdinaryNegativeOcticCommonBasis.action,OrdinaryNegativeOcticCommonBasis.action]
    funext z
    rw [ambient_value]
    ring
  rw [he]
  exact W.weight_affine_iff (v : AlgebraicComplex) (w : AlgebraicComplex)
    (fun h=>hv (Subtype.ext h)) (fun h=>hw (Subtype.ext h)) fourth p _

include literal hv hw fourth in
theorem evenBad (even : ∀j,Even (I.bundleSize p j))
    (bad : ¬Affine (fun z=>(f (word p z) : AlgebraicComplex))) : U.EvenBad H := by
  refine ⟨m,evenBlock H labels f v w literal p even,?_⟩
  exact fun h=>bad ((affine_iff H labels f v w literal p hv hw fourth).mp h)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedSignedSource
end
