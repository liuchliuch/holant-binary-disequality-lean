import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportTensorRecipe

/-! Overlay two unary resources with disjoint private variables. Each may
have odd boundary incidence: only the sum of their actual boundary counts
must be even. All other original ports keep their even degree. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockOverlay
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace C
export OrdinaryNegativeMixedBlockCompose (substitute count_map)
end C
namespace T
export OrdinaryNegativeAffineSupportTensorRecipe (plug)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s k l : ℕ} {b : ℕ→ℕ}

def leftPorts : Fin (1+k)→Bool ⊕ Fin (1+(k+l)) :=
  Fin.addCases (fun q=>.inr (Fin.castAdd (k+l) q))
    (fun j=>.inr (Fin.natAdd 1 (Fin.castAdd l j)))
def rightPorts : Fin (1+l)→Bool ⊕ Fin (1+(k+l)) :=
  Fin.addCases (fun q=>.inr (Fin.castAdd (k+l) q))
    (fun j=>.inr (Fin.natAdd 1 (Fin.natAdd k j)))

theorem left_boundary (q : Bool ⊕ Fin (1+k)) :
    C.substitute (leftPorts (k:=k) (l:=l)) q=Sum.inr 0 ↔ q=Sum.inr 0 := by
  cases q with
  | inl q => simp [C.substitute]
  | inr q =>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) q
    · have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [C.substitute,leftPorts,Fin.ext_iff]
    · simp [C.substitute,leftPorts,Fin.ext_iff]

theorem right_boundary (q : Bool ⊕ Fin (1+l)) :
    C.substitute (rightPorts (k:=k) (l:=l)) q=Sum.inr 0 ↔ q=Sum.inr 0 := by
  cases q with
  | inl q => simp [C.substitute]
  | inr q =>
    refine Fin.addCases (fun j=>?_) (fun j=>?_) q
    · have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [C.substitute,rightPorts,Fin.ext_iff]
    · simp [C.substitute,rightPorts,Fin.ext_iff]

theorem count_boundary {A B : Type*} [Fintype A] [BEq A] [LawfulBEq A] [DecidableEq A]
    [BEq B] [LawfulBEq B] [DecidableEq B] (xs : List A) (f : A→B) (a : A) (b : B)
    (h : ∀q,f q=b ↔q=a) : (xs.map f).count b=xs.count a := by
  rw [C.count_map]
  simp_rw [h]
  simp

theorem even_away_map {A B : Type*} [Fintype A] [BEq A] [LawfulBEq A] [DecidableEq A]
    [BEq B] [LawfulBEq B] [DecidableEq B] (xs : List A) (f : A→B) (a : A) (b q : B)
    (h : ∀p,p≠a→Even (xs.count p)) (hf : f a=b) (hne : q≠b) : Even ((xs.map f).count q) := by
  rw [C.count_map]
  apply Finset.even_sum
  intro p _
  by_cases hp : p=a
  · subst p
    simp [hf,hne.symm]
  · exact (h p hp).mul_right _

variable (first : Recipe (u:=1) (s:=s) (a:=fun _=>1+k) (b:=b))
variable (second : Recipe (u:=1) (s:=s) (a:=fun _=>1+l) (b:=b))

def recipe : Recipe (u:=1) (s:=s) (a:=fun _=>1+(k+l)) (b:=b) := fun _=>
  (first 0).map (T.plug leftPorts)++(second 0).map (T.plug rightPorts)

theorem ports_eq (i : Fin 1) : ports (recipe first second) i=
    (ports first 0).map (C.substitute (leftPorts (k:=k) (l:=l)))++
    (ports second 0).map (C.substitute (rightPorts (k:=k) (l:=l))) := by
  simp only [ports,recipe,List.flatMap_append,List.flatMap_map,List.map_flatMap,T.plug,
    Function.comp_def,List.map_ofFn]

theorem even_recipe (hf : ∀q,q≠Sum.inr 0→Even ((ports first 0).count q))
    (hg : ∀q,q≠Sum.inr 0→Even ((ports second 0).count q))
    (he : Even ((ports first 0).count (Sum.inr 0)+(ports second 0).count (Sum.inr 0))) :
    EvenRecipe (recipe first second) := by
  intro i q
  rw [ports_eq,List.count_append]
  by_cases hq : q=Sum.inr 0
  · subst q
    rw [count_boundary _ _ _ _ left_boundary,count_boundary _ _ _ _ right_boundary]
    exact he
  · exact (even_away_map _ _ _ _ q hf ((left_boundary (Sum.inr 0)).mpr rfl) hq).add
      (even_away_map _ _ _ _ q hg ((right_boundary (Sum.inr 0)).mpr rfl) hq)

variable {K : Type} [Field K] (H : (i : Fin s)→Signature K (b i.val))

theorem coefficient_eq (x : Fin (1+(k+l))→Bool) :
    coefficient H (recipe first second) 0 x=
      coefficient H first 0 (T.substitute leftPorts x)*coefficient H second 0 (T.substitute rightPorts x) := by
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient recipe
  rw [List.map_append,List.prod_append]
  apply congrArg₂ (·*·)
  all_goals
    simp only [List.map_map,Function.comp_def,T.plug]
    apply congrArg List.prod
    apply List.map_congr_left
    intro node _
    congr 1
    funext j
    cases node.2 j <;> simp [C.substitute,T.substitute]

theorem left_substitute (z : Fin 1→Bool) (x : Fin k→Bool) (y : Fin l→Bool) :
    T.substitute (leftPorts (k:=k) (l:=l)) (Fin.addCases z (Fin.addCases x y))=Fin.addCases z x := by
  funext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [T.substitute,leftPorts]

theorem right_substitute (z : Fin 1→Bool) (x : Fin k→Bool) (y : Fin l→Bool) :
    T.substitute (rightPorts (k:=k) (l:=l)) (Fin.addCases z (Fin.addCases x y))=Fin.addCases z y := by
  funext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [T.substitute,rightPorts]

theorem trace_eq (z : Fin 1→Bool) :
    M.trace H (k+l) (recipe first second) 0 z=M.trace H k first 0 z*M.trace H l second 0 z := by
  unfold M.trace
  rw [←(Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionMarginalValue.assignments k l).sum_comp,
    Fintype.sum_prod_type]
  simp only [Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionMarginalValue.assignments,
    Equiv.coe_fn_mk,coefficient_eq,left_substitute,right_substitute]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockOverlay
end
