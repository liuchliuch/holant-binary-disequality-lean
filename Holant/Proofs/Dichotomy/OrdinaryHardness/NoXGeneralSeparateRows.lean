import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionEvenProjection
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedPins

/-! A finite bundle whose positive and negative incidences are separately
even gives an actual unsigned even block on doubled variables. Individual
rows need not be even: the complete original-label bundle is checked. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateRows
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace S
export NoXSeparateSignedSource (rows ports_exact)
end S
namespace P
export NoXSeparateSignedProjection (signedCount constant_count positive_count negative_count opposite_value)
end P
namespace O
export NoXReciprocalSelectionEvenProjection (opposite opposite_affine)
end O
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s m k : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (ps : Fin m→Fin (b j.val)→Port k)

def rows : Recipe (u:=1) (s:=s) (a:=fun _=>k+k) (b:=b) :=
  fun _=>(List.ofFn (fun i : Fin m=>S.rows H j p0 p1 h0 h1 (ps i) 0)).flatten

theorem count (q : Bool ⊕ Fin (k+k)) : (ports (rows H j p0 p1 h0 h1 ps) 0).count q=
    ∑i : Fin m,(ports (S.rows H j p0 p1 h0 h1 (ps i)) 0).count q := by
  simp only [ports,rows,List.count_flatMap,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]

variable (even : ∀q bit,Even (∑i : Fin m,P.signedCount (ps i) q bit))
include even in
theorem balanced : EvenRecipe (rows H j p0 p1 h0 h1 ps) := by
  intro i q
  have hi : i=0 := Fin.eq_zero i
  subst i
  rw [count]
  simp_rw [S.ports_exact]
  cases q with
  | inl bit=>
      simp_rw [P.constant_count]
      rw [←Finset.mul_sum]
      exact Even.mul_right (by decide : Even 2) _
  | inr q=>
      refine Fin.addCases (fun a=>?_) (fun a=>?_) q
      · simp_rw [P.positive_count]
        exact even a false
      · simp_rw [P.negative_count]
        exact even a true

def block : B.Block (s:=s) (b:=b) (k+k) :=
  ⟨0,rows H j p0 p1 h0 h1 ps,balanced H j p0 p1 h0 h1 ps even⟩

theorem coefficient_value (z : Fin k→Bool) :
    coefficient H (rows H j p0 p1 h0 h1 ps) 0 (O.opposite z)=∏i,H j (word (ps i) z) := by
  have single (i : Fin m) : coefficient H (S.rows H j p0 p1 h0 h1 (ps i)) 0 (O.opposite z)=H j (word (ps i) z) := by
    rw [S.rows,OrdinaryNegativeMixedBlockRelabel.coefficient_eq]
    exact P.opposite_value (H j) (ps i) z
  change (((List.ofFn (fun i : Fin m=>S.rows H j p0 p1 h0 h1 (ps i) 0)).flatten).map
    (fun node=>H node.1 (fun a=>Sum.elim id (O.opposite z) (node.2 a)))).prod=_
  simp only [List.map_flatten,List.prod_flatten,List.map_ofFn,List.prod_ofFn]
  exact Finset.prod_congr rfl (fun i _=>single i)

theorem value (z : Fin k→Bool) :
    (block H j p0 p1 h0 h1 ps even).signature H (O.opposite z)=∏i,H j (word (ps i) z) := by
  change OrdinaryNegativeMixedBlockSource.trace (a:=fun _=>k+k) H 0 (rows H j p0 p1 h0 h1 ps) 0 (O.opposite z)=_
  rw [OrdinaryNegativeSparseMixingSource.trace_zero,coefficient_value]

include even h0 h1 in
theorem evenBad (bad : ¬Affine (fun z=>∏i,(H j (word (ps i) z) : AlgebraicComplex))) : B.EvenBad H := by
  refine ⟨k+k,block H j p0 p1 h0 h1 ps even,?_⟩
  intro affine
  have pulled:=affine.precompose O.opposite (O.opposite_affine (m:=k))
  have exactValue (z : Fin k→Bool) :
      ((block H j p0 p1 h0 h1 ps even).signature H (O.opposite z) : AlgebraicComplex)=
        ∏i,(H j (word (ps i) z) : AlgebraicComplex) := by
    rw [value]
    exact map_prod K.subtype _ _
  exact bad (by simpa only [exactValue] using pulled)

section Pins
variable {n : ℕ} (pins : Fin (b j.val)→Bool ⊕ Fin n)
variable (pure : OrdinaryNegativeSparseMinimalRank.PurePins pins)
variable (qs : Fin m→Fin n→Port k)
variable (separate : ∀q bit,Even (∑i : Fin m,P.signedCount (qs i) q bit))
include separate pure h0 h1 in
theorem pins_evenBad (bad : ¬Affine (fun z=>∏i,OrdinaryNegativeSparseMinimalRank.row (H j) pins (word (qs i) z))) :
    B.EvenBad H := by
  apply evenBad H j p0 p1 h0 h1 (fun i=>OrdinaryNegativeSignedRowsPins.signedCompose pins (qs i))
  · intro q bit
    simp_rw [NoXSeparateSignedPins.signedCount_compose pins pure]
    exact separate q bit
  · simpa only [OrdinaryNegativeSignedRowsPins.word_compose,OrdinaryNegativeSparseMinimalRank.row] using bad
end Pins


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateRows
end
