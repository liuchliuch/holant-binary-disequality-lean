import Holant.Dihedral.SupportIntegration.Patch
import Mathlib.Data.Fintype.Pigeonhole

/-! The weaker all-pairs projection condition implies global
self-orthogonality by the four-column pigeonhole argument. No global code
self-duality or fixed-edge endpoint structure is assumed. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 abbrev Remaining (i j : Fin n) := {k : Fin n // k ≠ i ∧ k ≠ j}

/-- Only equal-coordinate words must project into a matching direction. This
is strictly weaker than the four complementary-axis endpoint data. -/
 def MatchingProjections (D : BinaryCode n) : Prop :=
  ∀ i j : Fin n,i ≠ j → ∃ r : ℕ,∃ p : (Fin r × Bool) ≃ Remaining i j,
    ∀ x : BinaryVector n,x ∈ D → x i=x j →
      ∀ e,x (p (e,false)).val=x (p (e,true)).val

 theorem matching_sum_zero {ι : Type*} [Fintype ι] {r : ℕ}
    (p : (Fin r × Bool) ≃ ι) (x y : ι → ZMod 2)
    (hx : ∀ e,x (p (e,false))=x (p (e,true)))
    (hy : ∀ e,y (p (e,false))=y (p (e,true))) :
    (∑ i,x i*y i)=0 := by
  rw [←p.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro e _
  simp only [Fintype.sum_bool,hx e,hy e,ZModModule.add_self]

 theorem dot_split_pair (x y : BinaryVector n) (i j : Fin n) (hij : i ≠ j) :
    dot x y=x i*y i+x j*y j+∑ k : Remaining i j,x k.val*y k.val := by
  classical
  let f := fun k : Fin n => x k*y k
  have hrem : (∑ k : Remaining i j,f k.val)=∑ k ∈ (Finset.univ.erase i).erase j,f k := by
    exact (Finset.sum_subtype (F:=inferInstance) (p:=fun k : Fin n => k ≠ i ∧ k ≠ j)
      ((Finset.univ.erase i).erase j) (by intro k; simp [and_comm]) f).symm
  change (∑ k,f k)=f i+f j+∑ k : Remaining i j,f k.val
  rw [hrem]
  have hi := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) f (Finset.mem_univ i)
  have hj := Finset.add_sum_erase (Finset.univ.erase i) f (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)
  rw [←hi,←hj]
  ring

/-- For n>4 two coordinate columns of arbitrary x,y agree. Their deleted
contribution is zero, while the actual matching projection kills the rest. -/
 theorem selfOrthogonal_of_matchingProjections (D : BinaryCode n) (hn : 4<n)
    (hP : MatchingProjections D) :
    ∀ x : BinaryVector n,x ∈ D → ∀ y : BinaryVector n,y ∈ D → dot x y=0 := by
  intro x hx y hy
  obtain ⟨i,j,hij,hxy⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin n => (x k,y k)) (by
    simpa only [Fintype.card_prod,ZMod.card,Fintype.card_fin] using hn)
  have hxi : x i=x j := congrArg Prod.fst hxy
  have hyi : y i=y j := congrArg Prod.snd hxy
  obtain ⟨r,p,hp⟩ := hP i j hij
  have hzero := matching_sum_zero p (fun k => x k.val) (fun k => y k.val) (hp x hx hxi) (hp y hy hyi)
  rw [dot_split_pair x y i j hij,hxi,hyi,ZModModule.add_self,zero_add,hzero]

end Holant.Dihedral.SupportIntegration
