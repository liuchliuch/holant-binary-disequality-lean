import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases

/-! Exact cardinal accounting for distinct nonempty fibers of a finite map.
No geometric histogram or finite candidate completeness is assumed. -/
namespace Holant.Certificates.PlatonicAtlas
open Finset
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

 def mapFiber (D : Finset α) (f : α→β) (a : α) : Finset α :=
  D.filter (fun x => f x=f a)

 def fiberFamily (D : Finset α) (f : α→β) : Finset (Finset α) := D.image (mapFiber D f)

 theorem mapFiber_self (D : Finset α) (f : α→β) (a : α) (ha : a∈D) : a∈mapFiber D f a := by
  simp [mapFiber,ha]

 theorem mapFiber_eq_of_mem (D : Finset α) (f : α→β) (a b x : α)
    (hax : x∈mapFiber D f a) (hbx : x∈mapFiber D f b) :
    mapFiber D f a=mapFiber D f b := by
  have he : f a=f b := (mem_filter.mp hax).2.symm.trans (mem_filter.mp hbx).2
  simp only [mapFiber,he]

 theorem fiberFamily_nonempty (D : Finset α) (f : α→β) (S : Finset α)
    (hS : S∈fiberFamily D f) : S.Nonempty := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hS
  exact ⟨a,mapFiber_self D f a ha⟩

 theorem fiberFamily_pairwiseDisjoint (D : Finset α) (f : α→β) :
    (fiberFamily D f : Set (Finset α)).PairwiseDisjoint id := by
  intro S hS T hT hne
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hS
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hT
  exact hne (mapFiber_eq_of_mem D f a b x hx hy)

 theorem fiberFamily_union (D : Finset α) (f : α→β) :
    (fiberFamily D f).biUnion id=D := by
  ext x
  constructor
  · intro h
    obtain ⟨S,hS,hx⟩ := mem_biUnion.mp h
    obtain ⟨a,_,rfl⟩ := mem_image.mp hS
    exact (mem_filter.mp hx).1
  · intro hx
    exact mem_biUnion.mpr ⟨mapFiber D f x,mem_image.mpr ⟨x,hx,rfl⟩,mapFiber_self D f x hx⟩

 theorem fiberFamily_sum_card (D : Finset α) (f : α→β) :
    ∑S∈fiberFamily D f,S.card=D.card := by
  exact (card_biUnion (fiberFamily_pairwiseDisjoint D f)).symm.trans
    (congrArg Finset.card (fiberFamily_union D f))

 def fiberMultiplicity (D : Finset α) (f : α→β) (n : ℕ) : ℕ :=
  ((fiberFamily D f).filter (fun S => S.card=n)).card

 theorem fiberFamily_weighted_four (D : Finset α) (f : α→β)
    (hmax : ∀S∈fiberFamily D f,S.card≤4) :
    fiberMultiplicity D f 1+2*fiberMultiplicity D f 2+
      3*fiberMultiplicity D f 3+4*fiberMultiplicity D f 4=D.card := by
  have hsum : ∑S∈fiberFamily D f,S.card=
      ∑S∈fiberFamily D f,((if S.card=1 then 1 else 0)+
        (if S.card=2 then 2 else 0)+(if S.card=3 then 3 else 0)+(if S.card=4 then 4 else 0)) := by
    apply sum_congr rfl
    intro S hS
    have hp := (fiberFamily_nonempty D f S hS).card_pos
    have hm := hmax S hS
    interval_cases S.card <;> simp_all
  have hcount (n : ℕ) : (∑S∈fiberFamily D f,if S.card=n then n else 0)=
      n*fiberMultiplicity D f n := by
    rw [←Finset.sum_filter]
    simp [fiberMultiplicity,mul_comm]
  rw [sum_add_distrib,sum_add_distrib,sum_add_distrib,hcount,hcount,hcount,hcount,
    one_mul] at hsum
  exact hsum.symm.trans (fiberFamily_sum_card D f)

 theorem fiberMultiplicity_zero (D : Finset α) (f : α→β) (n : ℕ)
    (h : ∀S∈fiberFamily D f,S.card≠n) : fiberMultiplicity D f n=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  exact h S (mem_filter.mp hS).1 (mem_filter.mp hS).2

end
end Holant.Certificates.PlatonicAtlas
