import Holant.Dihedral.SupportIntegration.SelfDual
import Holant.ReedMuller.Steiner.Source

/-! Four nonempty endpoint slices make every original pair projection
surjective. Together with the derived self-duality this excludes weight two.
This stronger local-atlas setting must not be confused with an arbitrary
self-dual code having only equal-slice matching projections. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant.ReedMuller.LowArity Holant.ReedMuller.Steiner
variable {n : ℕ}

 theorem dot_indicator_pair (i j : Fin n) (hij : i ≠ j) (y : BinaryVector n) :
    dot (indicator {i,j}) y=y i+y j := by
  classical
  unfold dot
  have hh := Finset.sum_subset (Finset.subset_univ ({i,j} : Finset (Fin n)))
    (f:=fun k => indicator {i,j} k*y k) (by intro k _ hk; simp [indicator,hk])
  rw [←hh]
  simp [indicator,hij]

 theorem no_weight_two_of_pair_lifts (D : BinaryCode n) (hD : SelfDual D)
    (hlift : ∀ i j : Fin n,i ≠ j → ∃ y : BinaryVector n,y ∈ D ∧ y i=0 ∧ y j=1) :
    ∀ x : BinaryVector n,x ∈ D → (support x).card ≠ 2 := by
  classical
  intro x hx hw
  obtain ⟨i,j,hij,hS⟩ := Finset.card_eq_two.mp hw
  have hword := indicator_support x
  rw [hS] at hword
  obtain ⟨y,hy,hi,hj⟩ := hlift i j hij
  have hh := (hD x).mp hx y hy
  rw [←hword,dot_indicator_pair i j hij,hi,hj,zero_add] at hh
  exact one_ne_zero hh

 theorem LocalAtlas.no_weight_two {K : Type*} [Field K] {F : BinaryVector (n+2) → K}
    (A : LocalAtlas F) (hn : 4<n+2) :
    ∀ x : BinaryVector (n+2),x ∈ A.direction → (support x).card ≠ 2 :=
  no_weight_two_of_pair_lifts A.direction (A.selfDual hn)
    (fun i j hij => A.pair_lift i j hij 0 1)

end Holant.Dihedral.SupportIntegration
