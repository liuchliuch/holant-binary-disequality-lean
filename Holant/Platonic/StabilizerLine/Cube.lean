import Holant.Platonic.StabilizerLine.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The actual three-cube obstruction, with all seven off-origin coefficients
and the changed origin tied to the same two affine tensors. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem NormalForm.shift_mem {f : Signature ℂ n} (A : NormalForm f)
    (h0 : f (wordVector 0)≠0) : A.shift∈A.direction := by
  have h := A.direction.neg_mem ((A.support 0).mp h0)
  simpa using h

theorem NormalForm.support_linear {f : Signature ℂ n} (A : NormalForm f)
    (h0 : f (wordVector 0)≠0) (x : BinaryVector n) :
    f (wordVector x)≠0 ↔ x∈A.direction := by
  rw [A.support,Submodule.sub_mem_iff_left _ (A.shift_mem h0)]

theorem exists_cube_embedding (D : BinaryCode n) (hd : 3≤Module.finrank (ZMod 2) D) :
    ∃ E : BinaryVector 3 →ₗ[ZMod 2] BinaryVector n,
      Function.Injective E ∧ ∀ x,E x∈D := by
  obtain ⟨b,hb⟩ := exists_linearIndependent_of_le_finrank hd
  refine ⟨D.subtype.comp (Fintype.linearCombination (ZMod 2) b),?_,?_⟩
  · exact Subtype.val_injective.comp hb.fintypeLinearCombination_injective
  · intro x;exact (Fintype.linearCombination (ZMod 2) b x).property

theorem delta_cube_impossible {f g : Signature ℂ n} (A : NormalForm f) (B : NormalForm g)
    (c : ℂ) (hc : c≠0)
    (he : ∀ x : BinaryVector n,g (wordVector x)=(if x=0 then 1 else 0)+c*f (wordVector x))
    (E : BinaryVector 3 →ₗ[ZMod 2] BinaryVector n) (hE : Function.Injective E)
    (hs : ∀ x,f (wordVector (E x))≠0) : False := by
  let a : BinaryVector 3 := ![1,0,0]
  let b : BinaryVector 3 := ![0,1,0]
  let d : BinaryVector 3 := ![0,0,1]
  have hne (x : BinaryVector 3) (hx : x≠0) : E x≠0 := by
    intro h;exact hx (hE (h.trans E.map_zero.symm))
  have hg (x : BinaryVector 3) (hx : x≠0) : g (wordVector (E x))≠0 := by
    rw [he,if_neg (hne x hx),zero_add]
    exact mul_ne_zero hc (hs x)
  have hga := hg a (by decide)
  have hgb := hg b (by decide)
  have hgab := hg (a+b) (by decide)
  have hg0 : g (wordVector 0)≠0 := by
    have h := B.ternary (E a) (E b) (E (a+b)) hga hgb hgab
    simpa only [map_add,binary_self] using h
  have hf0 : f (wordVector 0)≠0 := by simpa using hs 0
  have hm (x : BinaryVector 3) : E x∈A.direction := (A.support_linear hf0 _).mp (hs x)
  have hmg (x : BinaryVector 3) (hx : x≠0) : E x∈B.direction :=
    (B.support_linear hg0 _).mp (hg x hx)
  have ha := A.phase_cube 0 (E a) (E b) (E d) ((A.support 0).mp hf0) (hm a) (hm b) (hm d)
  have hb := B.phase_cube 0 (E a) (E b) (E d) ((B.support 0).mp hg0)
    (hmg a (by decide)) (hmg b (by decide)) (hmg d (by decide))
  simp only [zero_add,←map_add] at ha hb
  have hx (x : BinaryVector 3) (hx : x≠0) :
      g (wordVector (E x))=c*f (wordVector (E x)) := by
    rw [he,if_neg (hne x hx),zero_add]
  rw [hx (a+b+d) (by decide),hx a (by decide),hx b (by decide),hx d (by decide),
    hx (a+b) (by decide),hx (a+d) (by decide),hx (b+d) (by decide),he 0,if_pos rfl] at hb
  have hn : c^3*f (wordVector (E (a+b)))*f (wordVector (E (a+d)))*
      f (wordVector (E (b+d)))≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (hs _)) (hs _)) (hs _)
  apply hn
  linear_combination c^4*ha-hb

end
end Holant.Platonic.StabilizerLine
