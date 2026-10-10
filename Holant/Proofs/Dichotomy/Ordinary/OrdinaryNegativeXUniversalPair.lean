import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalPairTable
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPrivateComposeSource

/-! Two actual odd private resources feed an arbitrary fixed even mixing
recipe. Their labels are only semantic inputs to the checked compiler: every
physical factor in the returned block belongs to the original table H. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalPair
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace R
export OrdinaryNegativeXUniversalResource (OddResource EvenBad)
end R
namespace C
export OrdinaryNegativeMixedBlockPrivateComposeCore (OddPrivate)
export OrdinaryNegativeMixedBlockPrivateComposeValue (rows)
export OrdinaryNegativeMixedBlockPrivateComposeSource (block block_value)
end C
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s n m d l : ℕ} {b : ℕ→ℕ}
variable (first : R.OddResource (s:=s) b n) (second : R.OddResource (s:=s) b m)

def resource (i : Fin 2) : R.OddResource (s:=s) b (arity n m i.val) :=
  match i with
  | ⟨0,_⟩=>first
  | ⟨1,_⟩=>second
  | ⟨j+2,h⟩=>False.elim (by omega)

def privateCounts (i : Fin 2) : ℕ := (resource first second i).privateCount

def inner (i : Fin 2) : Recipe (u:=1) (s:=s)
    (a:=fun _=>arity n m i.val+privateCounts first second i) (b:=b) :=
  (resource first second i).rows

theorem odd_private : C.OddPrivate (privateCounts first second) (inner first second) := by
  intro i
  exact ⟨(resource first second i).constant_even,
    (resource first second i).boundary_odd,(resource first second i).private_even⟩

variable (outer : Recipe (u:=1) (s:=2) (a:=fun _=>d+l) (b:=arity n m))
variable (ho : EvenRecipe outer)

def block : OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b) d :=
  C.block (n:=d) (l:=l) (b:=arity n m) (c:=b) outer
    (privateCounts first second) (inner first second) (odd_private first second) ho

variable {K : IntermediateField ℚ AlgebraicComplex}
variable (H : (j : Fin s)→Signature K (b j.val))

theorem rows_table : C.rows (b:=arity n m) (c:=b) (privateCounts first second) (inner first second) H=
    table (first.signature H) (second.signature H) := by
  funext i
  fin_cases i <;> rfl

/-- All per-occurrence private variables and original outer private variables
are included in the returned actual trace, with exact coefficients. -/
theorem block_value (z : Fin d→Bool) :
    (block first second outer ho).signature H z=
      M.trace (a:=fun _=>d) (table (first.signature H) (second.signature H)) l outer 0 z := by
  rw [block,C.block_value,rows_table]

theorem coefficient_map {L : Type} [CommSemiring L] (phi : K→+*L)
    (F : (i : Fin 2)→Signature K (arity n m i.val))
    (plain : Recipe (u:=1) (s:=2) (a:=fun _=>d) (b:=arity n m)) (z : Fin d→Bool) :
    phi (coefficient F plain 0 z)=coefficient (fun i x=>phi (F i x)) plain 0 z := by
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    map_list_prod,List.map_map,Function.comp_def]

/-- The ambient coefficient identity needed by semantic finite mixers. -/
theorem block_ambient
    (plain : Recipe (u:=1) (s:=2) (a:=fun _=>d) (b:=arity n m)) (hplain : EvenRecipe plain)
    (z : Fin d→Bool) :
    ((block (l:=0) first second plain hplain).signature H z : AlgebraicComplex)=
      coefficient (table (first.ambient H) (second.ambient H)) plain 0 z := by
  rw [block_value,OrdinaryNegativeSparseMixingSource.trace_zero]
  have hm := coefficient_map (n:=n) (m:=m) (K.subtype : K→+*AlgebraicComplex)
    (table (first.signature H) (second.signature H)) plain z
  have he : (fun i x=>(K.subtype : K→+*AlgebraicComplex)
      (table (first.signature H) (second.signature H) i x))=
        table (first.ambient H) (second.ambient H) := by
    funext i
    fin_cases i <;> rfl
  exact hm.trans (congrArg
    (fun T : (i : Fin 2)→Signature AlgebraicComplex (arity n m i.val)=>
      coefficient (u:=1) (s:=2) (a:=fun _=>d) (b:=arity n m) T plain 0 z) he)

/-- A proved bad finite even mixer yields an actual original-table even row. -/
theorem evenBad_of_coefficient
    (plain : Recipe (u:=1) (s:=2) (a:=fun _=>d) (b:=arity n m)) (hplain : EvenRecipe plain)
    (bad : ¬Affine (coefficient (table (first.ambient H) (second.ambient H)) plain 0)) :
    R.EvenBad H := by
  refine ⟨d,block (l:=0) first second plain hplain,?_⟩
  have he : (fun z=>((block (l:=0) first second plain hplain).signature H z : AlgebraicComplex))=
      coefficient (table (first.ambient H) (second.ambient H)) plain 0 :=
    funext (block_ambient first second H plain hplain)
  rwa [he]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalPair
end
