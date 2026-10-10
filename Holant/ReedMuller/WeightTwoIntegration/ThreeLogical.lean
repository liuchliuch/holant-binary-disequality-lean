import Holant.ReedMuller.WeightTwoIntegration.LogicalSlices
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalDeterminant

/-! Literal three-bit exceptional coefficients obtained from the actual
logical table and7.8; the original normalization scalar remains separate. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open scoped BigOperators

 theorem three_table_values (q : Signature ℂˣ 3) (rho : Fin 3 → ℂˣ) (kap : ℂˣ)
    (h0 : q (fun _=>false)=1) (hs : ∀i,q (DiagonalSlice.word {i})=rho i)
    (hp : ∀i j,i≠j → q (DiagonalSlice.word {i,j})=kap*rho i*rho j)
    (ht : q (fun _=>true)=kap*rho 0*rho 1*rho 2) :
    ∀a b c,(q ![a,b,c]:ℂ)=exceptionalH (fun i=>(rho i:ℂ)) kap a b c := by
  have e0 : DiagonalSlice.word ({0}:Finset (Fin 3))=![true,false,false] := by decide
  have e1 : DiagonalSlice.word ({1}:Finset (Fin 3))=![false,true,false] := by decide
  have e2 : DiagonalSlice.word ({2}:Finset (Fin 3))=![false,false,true] := by decide
  have e01 : DiagonalSlice.word ({0,1}:Finset (Fin 3))=![true,true,false] := by decide
  have e02 : DiagonalSlice.word ({0,2}:Finset (Fin 3))=![true,false,true] := by decide
  have e12 : DiagonalSlice.word ({1,2}:Finset (Fin 3))=![false,true,true] := by decide
  have ez : (![false,false,false] : Fin 3 → Bool)=(fun _=>false) := by decide
  have et : (![true,true,true] : Fin 3 → Bool)=(fun _=>true) := by decide
  intro a b c
  cases a <;> cases b <;> cases c
  · rw [ez]
    change (q (fun _=>false):ℂ)=1
    rw [h0]; rfl
  · change (q ![false,false,true]:ℂ)=(rho 2:ℂ)
    rw [←e2,hs]
  · change (q ![false,true,false]:ℂ)=(rho 1:ℂ)
    rw [←e1,hs]
  · change (q ![false,true,true]:ℂ)=(kap:ℂ)*(rho 1:ℂ)*(rho 2:ℂ)
    rw [←e12,hp 1 2 (by decide),Units.val_mul,Units.val_mul]
  · change (q ![true,false,false]:ℂ)=(rho 0:ℂ)
    rw [←e0,hs]
  · change (q ![true,false,true]:ℂ)=(kap:ℂ)*(rho 0:ℂ)*(rho 2:ℂ)
    rw [←e02,hp 0 2 (by decide),Units.val_mul,Units.val_mul]
  · change (q ![true,true,false]:ℂ)=(kap:ℂ)*(rho 0:ℂ)*(rho 1:ℂ)
    rw [←e01,hp 0 1 (by decide),Units.val_mul,Units.val_mul]
  · rw [et]
    change (q (fun _=>true):ℂ)=(kap:ℂ)*(rho 0:ℂ)*(rho 1:ℂ)*(rho 2:ℂ)
    rw [ht,Units.val_mul,Units.val_mul,Units.val_mul]

 namespace OriginalPairing
 variable {n : ℕ} {f : Signature ℂ n}

 def threeLogical (C : OriginalPairing f) (hc : C.count=3) (t : Fin 3 → Bool) : ℂ :=
   C.logical (fun i=>t (Fin.cast hc i))

 theorem three_parameters (C : OriginalPairing f) (H : Consistent f)
    (hd : EqualityDeck f) (hw : WeightedDeck f) (hn : 6≤n) (hc : C.count=3) :
    ∃rho : Fin 3 → ℂˣ,∃kap : ℂˣ,∀a b c,
      C.threeLogical hc ![a,b,c]=C.logical (fun _=>false)*
        exceptionalH (fun i=>(rho i:ℂ)) kap a b c := by
  let htwo : (2:ℂ)≠0 := by norm_num
  obtain ⟨rho,kap,hs,hp,ht⟩ := (C.logical_integration htwo H hd hw hn).2 hc
  let q : Signature ℂˣ 3 := fun t=>C.normalizedLogical htwo H hd hn (fun i=>t (Fin.cast hc i))
  have hzero : q (fun _=>false)=1 := C.normalizedLogical_zero htwo H hd hn
  have he := three_table_values q rho kap hzero hs hp ht
  refine ⟨rho,kap,?_⟩
  intro a b c
  have hh := he a b c
  change ((C.normalizedLogical htwo H hd hn (fun i=>![a,b,c] (Fin.cast hc i))):ℂ)=_ at hh
  simp only [normalizedLogical,Units.val_div_eq_div_val,Units.val_mk0] at hh
  exact ((div_eq_iff (C.logical_nonzero htwo H hd hn _)).mp hh).trans (mul_comm _ _)

 end OriginalPairing
end Holant.ReedMuller.WeightTwoIntegration
