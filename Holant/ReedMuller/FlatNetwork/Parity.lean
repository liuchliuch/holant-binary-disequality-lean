import Holant.ReedMuller.FlatNetwork.Projection

/-! Self-duality over the standard binary dot product forces even words,
the all-one word, and even ambient arity, without a dimension shortcut. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
variable {n : ℕ}

def ones (n : ℕ) : BinaryVector n := fun _ => 1
def binaryWeight (x : BinaryVector n) : ℕ := (Finset.univ.filter fun i => x i=1).card

theorem dot_self (x : BinaryVector n) : dot x x=∑ i,x i := by
  apply Finset.sum_congr rfl
  intro i _
  have H : ∀ a : ZMod 2,a*a=a := by decide
  exact H (x i)

theorem dot_ones (x : BinaryVector n) : dot (ones n) x=dot x x := by
  rw [dot_self]
  simp [dot,ones]

theorem selfDual_ones (D : BinaryCode n) (hD : SelfDual D) : ones n∈D := by
  apply (hD _).mpr
  intro x hx
  rw [dot_ones]
  exact (hD x).mp hx x hx

theorem selfDual_arity_even (D : BinaryCode n) (hD : SelfDual D) : Even n := by
  have H := (hD (ones n)).mp (selfDual_ones D hD) (ones n) (selfDual_ones D hD)
  have hz : (n : ZMod 2)=0 := by simpa [dot,ones] using H
  have hd : 2∣n := (ZMod.natCast_eq_zero_iff n 2).mp hz
  exact even_iff_two_dvd.mpr hd

theorem cast_binaryWeight (x : BinaryVector n) : (binaryWeight x : ZMod 2)=dot x x := by
  rw [dot_self]
  unfold binaryWeight
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  have H : ∀ a : ZMod 2,(if a=1 then (1:ZMod 2) else 0)=a := by decide
  exact H (x i)

theorem selfDual_weight_even (D : BinaryCode n) (hD : SelfDual D)
    (x : BinaryVector n) (hx : x∈D) : Even (binaryWeight x) := by
  have hz : (binaryWeight x : ZMod 2)=0 := by
    rw [cast_binaryWeight]
    exact (hD x).mp hx x hx
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ 2).mp hz)

end
end Holant.ReedMuller.FlatNetwork
