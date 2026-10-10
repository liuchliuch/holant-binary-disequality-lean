import Holant.ReedMuller.WeightTwoIntegration.Logical
import Holant.ReedMuller.WeightTwoIntegration.WeightedDeck
import Holant.ReedMuller.WeightTwoIntegration.IndexedProduct

/-! Actual weighted cross cards give the exact simple diagonal slices required
by7.8. Every unit is constructed from a proved nonzero original coefficient. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ} {f : Signature K n}
namespace OriginalPairing

 def normalizedLogical (C : OriginalPairing f) (htwo : (2:K)≠0) (H : Consistent f)
    (hd : EqualityDeck f) (hn : 6≤n) (t : Fin C.count → Bool) : Kˣ :=
  Units.mk0 (C.logical t) (C.logical_nonzero htwo H hd hn t)/
    Units.mk0 (C.logical (fun _=>false)) (C.logical_nonzero htwo H hd hn _)

 theorem normalizedLogical_zero (C : OriginalPairing f) (htwo : (2:K)≠0) (H : Consistent f)
    (hd : EqualityDeck f) (hn : 6≤n) : C.normalizedLogical htwo H hd hn (fun _=>false)=1 := by
  simp [normalizedLogical]

 theorem logical_diagonal_simple (C : OriginalPairing f) (htwo : (2:K)≠0) (H : Consistent f)
    (hd : EqualityDeck f) (hw : WeightedDeck f) (hn : 6≤n) (i j : Fin C.count) (hij : i≠j) :
    DiagonalSlice.SimpleDiagonal (C.normalizedLogical htwo H hd hn) i j := by
  let u := C.ports (i,false)
  let v := C.ports (i,true)
  let k := C.ports (j,false)
  have huv : (weightGraph f).Adj u v := C.port_edge i
  have huk : u≠k := by intro h; exact hij (congrArg Prod.fst (C.ports.injective h))
  have hvk : v≠k := by intro h; exact hij (congrArg Prod.fst (C.ports.injective h))
  obtain ⟨P,hP⟩ := (hw u k huk false).resolve_left (cross_card_nonzero htwo H u v k huv huk hvk)
  let label : Fin P.edges → Fin C.count := fun e => (C.ports.symm (P.ports (e,false)).val).1
  let c : Kˣ := P.scalar/Units.mk0 (2*C.logical (fun _=>false))
    (mul_ne_zero htwo (C.logical_nonzero htwo H hd hn _))
  apply indexed_product_simple (C.normalizedLogical htwo H hd hn) i j hij c label P.diagonal
  intro t ht
  let x : Fin n → Bool := pairedWord C.ports t
  let y : Remaining u k → Bool := fun p => x p.val
  have hxuv : x u=x v := by simp only [x,u,v,pairedWord_port]
  have hxuk : x u=x k := by simpa only [x,u,k,pairedWord_port] using ht
  have he : card f u k false y=2*C.logical t := cross_unique_lift H u v k huv hvk x hxuv hxuk
  have hpne : P.value y≠0 := by
    rw [←hP,he]
    exact mul_ne_zero htwo (C.logical_nonzero htwo H hd hn t)
  have hval := P.value_eq_diagonal y hpne
  rw [←hP,he] at hval
  have hval' : 2*C.logical t=(P.scalar:K)*(∏e,(P.diagonal e (t (label e)):K)) := by
    simpa only [WeightedProduct.diagonalValue,Units.val_mul,Units.coe_prod,y,x,pairedWord,label] using hval
  apply Units.ext
  change ((Units.mk0 (C.logical t) _ / Units.mk0 (C.logical (fun _=>false)) _:Kˣ):K)=_
  simp only [c,Units.val_div_eq_div_val,Units.val_mk0,Units.val_mul,Units.coe_prod]
  change C.logical t/C.logical (fun _=>false)=
    (P.scalar:K)/(2*C.logical (fun _=>false))*(∏e,(P.diagonal e (t (label e)):K))
  field_simp [htwo,C.logical_nonzero htwo H hd hn (fun _=>false)]
  linear_combination hval'

/-- The complete generic7.8 alternatives now have their hypotheses derived
from the original proper cards. -/
 theorem logical_integration (C : OriginalPairing f) (htwo : (2:K)≠0) (H : Consistent f)
    (hd : EqualityDeck f) (hw : WeightedDeck f) (hn : 6≤n) :
    (4≤C.count → ∃rho : Fin C.count → Kˣ,∀t,
      C.normalizedLogical htwo H hd hn t=∏i,rho i^(if t i then 1 else 0 : ℕ)) ∧
    (∀e : C.count=3,∃rho : Fin 3 → Kˣ,∃kap : Kˣ,
      (∀i,C.normalizedLogical htwo H hd hn (fun k=>DiagonalSlice.word {i} (Fin.cast e k))=rho i) ∧
      (∀i j,i≠j → C.normalizedLogical htwo H hd hn
        (fun k=>DiagonalSlice.word {i,j} (Fin.cast e k))=kap*rho i*rho j) ∧
      C.normalizedLogical htwo H hd hn (fun _=>true)=kap*rho 0*rho 1*rho 2) := by
  constructor
  · intro h4
    exact DiagonalSlice.diagonal_slice_integration h4 _ (C.normalizedLogical_zero htwo H hd hn)
      (C.logical_diagonal_simple htwo H hd hw hn)
  · intro e
    have generic {r : ℕ} (q : (Fin r → Bool) → Kˣ) (hz : q (fun _=>false)=1)
        (hs : ∀i j,i≠j → DiagonalSlice.SimpleDiagonal q i j) (e : r=3) :
        ∃rho : Fin 3 → Kˣ,∃kap : Kˣ,
          (∀i,q (fun k=>DiagonalSlice.word {i} (Fin.cast e k))=rho i) ∧
          (∀i j,i≠j → q (fun k=>DiagonalSlice.word {i,j} (Fin.cast e k))=kap*rho i*rho j) ∧
          q (fun _=>true)=kap*rho 0*rho 1*rho 2 := by
      subst r
      simpa using DiagonalSlice.diagonal_slice_three q hz hs
    exact generic _ (C.normalizedLogical_zero htwo H hd hn)
      (C.logical_diagonal_simple htwo H hd hw hn) e


end OriginalPairing
end Holant.ReedMuller.WeightTwoIntegration
