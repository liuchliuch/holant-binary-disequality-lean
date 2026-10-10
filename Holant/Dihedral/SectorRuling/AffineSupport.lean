import Holant.Dihedral.TwoCardLocalization.MonomialUniqueness

/-! The half-intersection bound used by source6.8 follows from literal affine
support closure. No common support, direction or matching is assumed. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Dihedral.EndpointParallelogram
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

def AffineClosed (S : Finset V) : Prop :=
  ∀ x ∈ S,∀ y ∈ S,∀ z ∈ S,x+y+z ∈ S

private theorem cancel_pair (x a c : V) : (x+a+c)+x+c=a := by
  calc
    (x+a+c)+x+c=a+(x+x)+(c+c) := by abel
    _ = a := by rw [ZModModule.add_self,ZModModule.add_self]; simp

/-- Two different affine supports of equal size intersect in at most half
that size. The proof constructs a disjoint translate of the intersection. -/
theorem affine_intersection_half (S T : Finset V) (hS : AffineClosed S) (hT : AffineClosed T)
    (hcard : S.card=T.card) (hne : S ≠ T) : 2*(S∩T).card ≤ S.card := by
  classical
  by_cases hi : (S∩T).Nonempty
  · obtain ⟨c,hc⟩ := hi
    obtain ⟨a,haS,haT⟩ : ∃ a,a ∈ S ∧ a ∉ T := by
      by_contra hn
      push_neg at hn
      exact hne (Finset.eq_of_subset_of_card_le hn (by omega))
    let shift : V → V := fun x => x+a+c
    have hinj : Function.Injective shift := by
      intro x y h
      exact add_right_cancel (add_right_cancel h)
    have hsub : (S∩T) ∪ (S∩T).image shift ⊆ S := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx|hx
      · exact (Finset.mem_inter.mp hx).1
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
        exact hS y (Finset.mem_inter.mp hy).1 a haS c (Finset.mem_inter.mp hc).1
    have hdis : Disjoint (S∩T) ((S∩T).image shift) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz'
      have ht := hT (shift x) (Finset.mem_inter.mp hz).2 x (Finset.mem_inter.mp hx).2 c (Finset.mem_inter.mp hc).2
      apply haT
      simpa only [shift,cancel_pair] using ht
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis,Finset.card_image_of_injective _ hinj] at hh
    omega
  · have hz : S∩T=∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    simp [hz]

/-- Actual affine cosets supply the closure hypothesis of the finite-set bound. -/
theorem affineClosed_of_coset (S : Finset V) (L : Submodule (ZMod 2) V) (a : V)
    (hS : ∀ x,x ∈ S ↔ x ∈ coset L a) : AffineClosed S := by
  intro x hx y hy z hz
  apply (hS _).mpr
  have hx' := (hS x).mp hx
  have hy' := (hS y).mp hy
  have hz' := (hS z).mp hz
  change x+a ∈ L at hx'
  change y+a ∈ L at hy'
  change z+a ∈ L at hz'
  change x+y+z+a ∈ L
  have hh := L.add_mem (L.add_mem hx' hy') hz'
  have he : (x+a)+(y+a)+(z+a)=x+y+z+a := by
    calc
      (x+a)+(y+a)+(z+a)=(x+y+z+a)+(a+a) := by abel
      _ = _ := by rw [ZModModule.add_self]; simp
  rwa [he] at hh

end Holant.Dihedral.SectorRuling
