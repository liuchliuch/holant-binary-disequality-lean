import Holant.ReedMuller.FlatNetwork.Coordinates

/-! Flat/self-dual structure is invariant under the exact original-port
bijection, with the shift transported explicitly. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

def coordinateMap (e : Fin n ≃ Fin m) : BinaryVector m →ₗ[ZMod 2] BinaryVector n where
  toFun x := fun i => x (e i)
  map_add' := by intros;rfl
  map_smul' := by intros;rfl

def relabelCode (e : Fin n ≃ Fin m) (D : BinaryCode n) : BinaryCode m := D.comap (coordinateMap e)

theorem dot_coordinateMap (e : Fin n ≃ Fin m) (x y : BinaryVector m) :
    dot (coordinateMap e x) (coordinateMap e y)=dot x y := by
  exact Equiv.sum_comp e (fun j => x j*y j)

theorem relabelCode_selfDual (e : Fin n ≃ Fin m) (D : BinaryCode n) (hD : SelfDual D) :
    SelfDual (relabelCode e D) := by
  intro x
  constructor
  · intro hx y hy
    have H := (hD (coordinateMap e x)).mp hx (coordinateMap e y) hy
    simpa only [dot_coordinateMap] using H
  · intro hx
    apply (hD (coordinateMap e x)).mpr
    intro y hy
    let z : BinaryVector m := fun i => y (e.symm i)
    have hz : coordinateMap e z=y := by funext i;simp [coordinateMap,z]
    have hm : z∈relabelCode e D := by change coordinateMap e z∈D;rwa [hz]
    have H := hx z hm
    rw [←dot_coordinateMap e x z,hz] at H
    exact H

theorem flat_reindex (e : Fin n ≃ Fin m) (f : Signature ℂ n) (hf : Flat f) :
    Flat (Tensor.reindex e f) := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  refine ⟨c,(fun i => a (e.symm i)),relabelCode e D,relabelCode_selfDual e D hD,?_⟩
  funext x
  simp only [Tensor.reindex,flatSignature]
  have he : (fun i => bit (x (e i))-a i)=
      coordinateMap e (fun i => bit (x i)-a (e.symm i)) := by
    funext i
    simp [coordinateMap]
  rw [he]
  rfl

theorem flatOrZero_reindex (e : Fin n ≃ Fin m) (f : Signature ℂ n) (hf : FlatOrZero f) :
    FlatOrZero (Tensor.reindex e f) := by
  rcases hf with rfl | h
  · left;rfl
  · exact Or.inr (flat_reindex e f h)

end
end Holant.ReedMuller.FlatNetwork
