import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockValidity

/-! Literal heterogeneous recipe substitution. The resulting blocks keep every
original label, occurrence and constant port. Semantic substitution and even
incidence are proved independently of any counting-hardness premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockCompose
open Holant
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {u v s : ℕ} {a b c : ℕ→ℕ}

def substitute {m n : ℕ} (p : Fin m→Bool ⊕ Fin n) : Bool ⊕ Fin m→Bool ⊕ Fin n :=
  Sum.elim Sum.inl p

def plug {i : Fin u} {j : Fin v} (p : Fin (b j.val)→Bool ⊕ Fin (a i.val))
    (node : Node (u:=v) (s:=s) (a:=b) (b:=c) j) : Node (u:=u) (s:=s) (a:=a) (b:=c) i :=
  ⟨node.1,fun k=>substitute p (node.2 k)⟩

def compose (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) : Recipe (u:=u) (s:=s) (a:=a) (b:=c) :=
  fun i=>(outer i).flatMap (fun node=>(inner node.1).map (plug node.2))

variable {K : Type} [CommSemiring K]

theorem coefficient_compose (H : (j : Fin s)→Signature K (c j.val))
    (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) (i : Fin u) (x : Fin (a i.val)→Bool) :
    coefficient H (compose outer inner) i x=coefficient (coefficient H inner) outer i x := by
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient compose
  rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro node _
  simp only [List.map_map,Function.comp_def,plug]
  apply congrArg List.prod
  apply List.map_congr_left
  intro subnode _
  congr 1
  funext j
  cases h : subnode.2 j <;> simp [substitute,h]

theorem ports_compose (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) (i : Fin u) :
    ports (compose outer inner) i=
      (outer i).flatMap (fun node=>(ports inner node.1).map (substitute node.2)) := by
  simp only [ports,compose,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,
    Function.comp_def,plug,List.map_ofFn]

theorem count_map {A B : Type*} [Fintype A] [BEq A] [LawfulBEq A] [DecidableEq A] [BEq B] [LawfulBEq B] [DecidableEq B]
    (xs : List A) (f : A→B) (k : B) :
    (xs.map f).count k=∑a : A,xs.count a*(if f a=k then 1 else 0) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons,List.count_cons,ih,add_mul,Finset.sum_add_distrib]
      congr 1
      simp only [beq_iff_eq,ite_mul,one_mul,zero_mul]
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        simp [Ne.symm hy]
      · simp

theorem even_map {A B : Type*} [Fintype A] [BEq A] [LawfulBEq A] [DecidableEq A] [BEq B] [LawfulBEq B] [DecidableEq B]
    (xs : List A) (h : ∀a,Even (xs.count a)) (f : A→B) (k : B) :
    Even ((xs.map f).count k) := by
  rw [count_map]
  apply Finset.even_sum
  intro a _
  exact (h a).mul_right _

theorem even_flatMap {A B : Type*} [BEq B] [LawfulBEq B] [DecidableEq B] (xs : List A) (f : A→List B)
    (h : ∀a∈xs,∀b,Even ((f a).count b)) (b : B) : Even ((xs.flatMap f).count b) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.flatMap_cons,List.count_append]
      exact (h a (by simp) b).add (ih (fun a ha=>h a (by simp [ha])))

theorem even_compose (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) (hi : EvenRecipe inner) :
    EvenRecipe (compose outer inner) := by
  intro i q
  rw [ports_compose]
  apply even_flatMap
  intro node _ q
  exact even_map _ (hi node.1) _ q

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockCompose
end
