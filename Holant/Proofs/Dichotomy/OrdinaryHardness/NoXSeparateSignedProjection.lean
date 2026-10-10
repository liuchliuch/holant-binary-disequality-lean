import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedPortsIncidence
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockRelabel
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Keep positive and negative bundle ports physically separate. This actual
projection uses one unchanged row and pins, with no X or weighted anti node.
Its two signed incidence counts are proved independently and the original
coefficient is recovered on the literal opposite assignment. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXSeparateSignedProjection
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
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
variable {n m : ℕ}

def arity (n j : ℕ) : ℕ := if j=0 then n else 1

def rowPort (p : Fin n→Port m) (i : Fin n) : Bool ⊕ Fin (m+m) :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,false)=>.inr (Fin.castAdd m j)
  | .inr (j,true)=>.inr (Fin.natAdd m j)

def pinNode (bit : Bool) (q : Bool ⊕ Fin (m+m)) :
    Node (u:=1) (s:=3) (a:=fun _=>m+m) (b:=arity n) 0 :=
  if bit then ⟨2,fun _=>q⟩ else ⟨1,fun _=>q⟩

def fixedRows (p : Fin n→Port m) (i : Fin n) :
    List (Node (u:=1) (s:=3) (a:=fun _=>m+m) (b:=arity n) 0) :=
  match p i with
  | .inl bit=>[pinNode bit (.inl bit)]
  | .inr _=>[]

def recipe (p : Fin n→Port m) : Recipe (u:=1) (s:=3) (a:=fun _=>m+m) (b:=arity n) :=
  fun _=>⟨0,rowPort p⟩::(List.ofFn (fixedRows p)).flatten

def signedCount (p : Fin n→Port m) (j : Fin m) (bit : Bool) : ℕ :=
  ∑i,if p i=.inr (j,bit) then 1 else 0

def fixedCount (p : Fin n→Port m) (i : Fin n) (q : Bool ⊕ Fin (m+m)) : ℕ :=
  match p i with
  | .inl bit=>if Sum.inl bit=q then 1 else 0
  | .inr _=>0

theorem pin_count (bit : Bool) (p q : Bool ⊕ Fin (m+m)) :
    (List.ofFn (pinNode (n:=n) bit p).2).count q=if p=q then 1 else 0 := by
  rw [O.count_ofFn]
  cases bit <;> change (∑_i : Fin 1,if p=q then 1 else 0)=_
  all_goals rw [Fin.sum_univ_one]

theorem fixed_count (p : Fin n→Port m) (i : Fin n) (q : Bool ⊕ Fin (m+m)) :
    ((fixedRows p i).map (fun node=>(List.ofFn node.2).count q)).sum=fixedCount p i q := by
  cases h : p i with
  | inl bit=>
      simp only [fixedRows,fixedCount,h,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      exact pin_count bit (.inl bit) q
  | inr v=>simp [fixedRows,fixedCount,h]

theorem total_count (p : Fin n→Port m) (q : Bool ⊕ Fin (m+m)) :
    (ports (recipe p) 0).count q=∑i,((if rowPort p i=q then 1 else 0)+fixedCount p i q) := by
  simp only [ports,recipe,List.flatMap_cons,List.count_append,List.count_flatMap,
    List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rw [O.count_ofFn]
  simp only [fixed_count,Finset.sum_add_distrib]
  rfl

theorem constant_count (p : Fin n→Port m) (bit : Bool) :
    (ports (recipe p) 0).count (.inl bit)=2*(∑i,if p i=.inl bit then 1 else 0) := by
  rw [total_count,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i with
  | inl v=>by_cases hv : v=bit <;> simp [rowPort,fixedCount,h,hv]
  | inr v=>rcases v with ⟨j,sgn⟩;cases sgn <;> simp [rowPort,fixedCount,h]

theorem positive_ne_negative (i j : Fin m) : Fin.castAdd m i≠Fin.natAdd m j := by
  intro h
  have hv:=congrArg Fin.val h
  simp at hv
  omega

theorem positive_count (p : Fin n→Port m) (j : Fin m) :
    (ports (recipe p) 0).count (.inr (Fin.castAdd m j))=signedCount p j false := by
  rw [total_count,signedCount]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i with
  | inl bit=>simp [rowPort,fixedCount,h]
  | inr v=>
      rcases v with ⟨k,sgn⟩
      cases sgn
      · simp [rowPort,fixedCount,h,Fin.castAdd_inj]
      · have hn : Fin.natAdd m k≠Fin.castAdd m j := (positive_ne_negative j k).symm
        simpa only [rowPort,h,fixedCount,Sum.inr.injEq,Prod.mk.injEq,Bool.true_eq_false,
          and_false,ite_false,Nat.add_zero] using ite_eq_right hn

theorem negative_count (p : Fin n→Port m) (j : Fin m) :
    (ports (recipe p) 0).count (.inr (Fin.natAdd m j))=signedCount p j true := by
  rw [total_count,signedCount]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i with
  | inl bit=>simp [rowPort,fixedCount,h]
  | inr v=>
      rcases v with ⟨k,sgn⟩
      cases sgn
      · have hn : Fin.castAdd m k≠Fin.natAdd m j := positive_ne_negative k j
        simpa only [rowPort,h,fixedCount,Sum.inr.injEq,Prod.mk.injEq,Bool.false_eq_true,
          and_false,ite_false,Nat.add_zero] using ite_eq_right hn
      · simp [rowPort,fixedCount,h]

section Values
variable {K : Type} [Field K]

def table (f : Signature K n) (j : Fin 3) : Signature K (arity n j.val) :=
  match j with
  | ⟨0,_⟩=>f
  | ⟨1,_⟩=>OrdinaryNegativeSignedPortsCore.pin false
  | ⟨2,_⟩=>OrdinaryNegativeSignedPortsCore.pin true
  | ⟨j+3,h⟩=>False.elim (by omega)

theorem pin_value (f : Signature K n) (bit : Bool) (p : Bool ⊕ Fin (m+m)) (z : Fin (m+m)→Bool) :
    table f (pinNode bit p).1 (T.substitute (pinNode bit p).2 z)=
      if Sum.elim id z p=bit then 1 else 0 := by
  cases bit <;> rfl

theorem coefficient_value (f : Signature K n) (p : Fin n→Port m) (z : Fin (m+m)→Bool) :
    coefficient (table f) (recipe p) 0 z=f (T.substitute (rowPort p) z) := by
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    recipe,List.map_cons,List.prod_cons,List.map_flatten,List.prod_flatten,List.map_ofFn,List.prod_ofFn]
  have hp (i : Fin n) : ((fixedRows p i).map (fun node=>table f node.1 (T.substitute node.2 z))).prod=1 := by
    cases h : p i with
    | inl bit=>simp [fixedRows,h,pin_value]
    | inr v=>simp [fixedRows,h]
  change f (T.substitute (rowPort p) z)*(∏i,((fixedRows p i).map
    (fun node=>table f node.1 (T.substitute node.2 z))).prod)=_
  simp only [hp,Finset.prod_const_one,mul_one]

theorem opposite_value (f : Signature K n) (p : Fin n→Port m) (z : Fin m→Bool) :
    coefficient (table f) (recipe p) 0 (Fin.addCases z (fun j=>!(z j)))=f (word p z) := by
  rw [coefficient_value]
  congr 1
  funext i
  cases h : p i with
  | inl bit=>simp [T.substitute,rowPort,word,h]
  | inr v=>
      rcases v with ⟨j,sgn⟩
      cases sgn <;> simp only [T.substitute,rowPort,word,h,Sum.elim_inr,
        Fin.addCases_left,Fin.addCases_right,Bool.false_xor,Bool.true_xor]
end Values


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXSeparateSignedProjection
end
