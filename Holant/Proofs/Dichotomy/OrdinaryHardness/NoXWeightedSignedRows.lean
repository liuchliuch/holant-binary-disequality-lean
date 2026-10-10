import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedSignedSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsPins

/-! Products of signed restrictions use only unchanged original row labels,
actual weighted antidiagonals and pins. Flattening is exact, including its
entire Affine phase multiplier when the anti fourth powers agree. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedSignedRows
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSignedPortsCore (Port word arity)
open scoped BigOperators
namespace W
export NoXWeightedSignedPorts (table weight trace_value weight_affine_iff)
end W
namespace C
export OrdinaryNegativeMixedBlockCompose (compose coefficient_compose)
end C
namespace Q
export OrdinaryNegativeSignedRowsCore (flatten expand tensor recipe recipe_ports even_recipe bundleSize_flatten)
end Q
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe even_recipe coefficient_eq ports_eq)
end R
namespace P
export OrdinaryNegativeSignedRowsPins (signedCompose lifted lifted_even word_compose)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m r : ℕ} {K : Type} [Field K]

theorem expand_value (f : Signature K n) (v w : K) (i : Fin 4) (z : Fin (arity (r*n) i.val)→Bool) :
    coefficient (W.table f v w) (Q.expand r n) i z=W.table (Q.tensor f r) v w i z := by
  fin_cases i <;>
    simp [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
      Q.expand,W.table,Q.tensor,List.map_ofFn,List.prod_ofFn]
  rfl

theorem coefficient_value (f : Signature K n) (v w : K) (p : Fin r→Fin n→Port m)
    (z : Fin (m+r*n)→Bool) :
    coefficient (W.table f v w) (Q.recipe p) 0 z=
      coefficient (W.table (Q.tensor f r) v w) (OrdinaryNegativeSignedPortsCore.recipe (Q.flatten p)) 0 z := by
  rw [Q.recipe,C.coefficient_compose]
  have he : coefficient (W.table f v w) (Q.expand r n)=W.table (Q.tensor f r) v w := by
    funext i x
    exact expand_value f v w i x
  rw [he]

theorem trace_value (f : Signature K n) (v w : K) (p : Fin r→Fin n→Port m) (z : Fin m→Bool) :
    (∑y : Fin (r*n)→Bool,coefficient (W.table f v w) (Q.recipe p) 0 (Fin.addCases z y))=
      W.weight v w (Q.flatten p) z*∏i,f (word (p i) z) := by
  simp_rw [coefficient_value]
  change NoXWeightedSignedPorts.trace (Q.tensor f r) v w (Q.flatten p) z=_
  rw [W.trace_value]
  congr 1
  unfold Q.tensor
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  funext j
  simp [word,Q.flatten]

section Original
variable {K : IntermediateField ℚ AlgebraicComplex} {s N : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (f : Signature K N) (v w : K)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,W.table f v w i⟩)
variable (pins : Fin N→Bool ⊕ Fin n) (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (p : Fin r→Fin n→Port m)
variable (even : ∀j,Even (∑i,OrdinaryNegativeSignedPortsIncidence.bundleSize (p i) j))

def block : OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b) m where
  privateCount := r*N
  rows := R.exactRecipe labels (W.table f v w) H literal (Q.recipe (P.lifted pins p))
  balanced := R.even_recipe labels (fun i=>congrArg Sigma.fst (literal i)) _
    (Q.even_recipe _ (P.lifted_even pins pure p even))

theorem block_value (z : Fin m→Bool) :
    (block H labels f v w literal pins pure p even).signature H z=
      W.weight v w (Q.flatten (P.lifted pins p)) z*
      ∏i,f (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute
        pins (word (p i) z)) := by
  unfold OrdinaryNegativeSparseMixingSource.Block.signature block OrdinaryNegativeMixedBlockSource.trace
  simp_rw [R.coefficient_eq]
  rw [trace_value]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [P.lifted,P.word_compose]

theorem ambient_value (z : Fin m→Bool) :
    ((block H labels f v w literal pins pure p even).signature H z : AlgebraicComplex)=
      W.weight (v : AlgebraicComplex) (w : AlgebraicComplex) (Q.flatten (P.lifted pins p)) z*
      ∏i,OrdinaryNegativeSparseMinimalRank.row f pins (word (p i) z) := by
  rw [block_value,IntermediateField.coe_mul,NoXWeightedSignedSource.weight_coe]
  congr 1
  exact map_prod K.subtype _ _

variable (hv : v≠0) (hw : w≠0) (fourth : (v : AlgebraicComplex)^4=(w : AlgebraicComplex)^4)
include literal pure even hv hw fourth in
theorem evenBad (bad : ¬Affine (fun z=>∏i,OrdinaryNegativeSparseMinimalRank.row f pins (word (p i) z))) :
    OrdinaryNegativeXUniversalResource.EvenBad H := by
  refine ⟨m,block H labels f v w literal pins pure p even,?_⟩
  intro aff
  simp only [ambient_value] at aff
  exact bad ((W.weight_affine_iff (v : AlgebraicComplex) (w : AlgebraicComplex)
    (fun h=>hv (Subtype.ext h)) (fun h=>hw (Subtype.ext h)) fourth _ _).mp aff)
end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedSignedRows
end
