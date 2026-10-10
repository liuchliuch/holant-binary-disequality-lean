import Holant.ReedMuller.AffineRadon.NormalForm
import Holant.ReedMuller.LowArity.HalfDimension

/-! Uniqueness and dimensions of the actual affine direction of a tensor
support. This relates geometric card images to genuine flat-card hypotheses. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem affine_support_direction_unique {K : Type*} [Zero K] (f : BinaryVector n → K)
    (a b : BinaryVector n) (D E : BinaryCode n)
    (hD : ∀ x,f x≠0 ↔ x-a∈D) (hE : ∀ x,f x≠0 ↔ x-b∈E) : D=E := by
  have hab : a-b∈E := (hE a).mp ((hD a).mpr (by simp))
  have hba : b-a∈D := (hD b).mp ((hE b).mpr (by simp))
  apply le_antisymm
  · intro u hu
    have hf : f (a+u)≠0 := (hD _).mpr (by simpa [add_sub_cancel_left] using hu)
    have hh := E.sub_mem ((hE _).mp hf) hab
    have he : (a+u-b)-(a-b)=u := by abel
    rwa [he] at hh
  · intro u hu
    have hf : f (b+u)≠0 := (hE _).mpr (by simpa [add_sub_cancel_left] using hu)
    have hh := D.sub_mem ((hD _).mp hf) hba
    have he : (b+u-a)-(b-a)=u := by abel
    rwa [he] at hh

 theorem selfDual_half_dimension (D : BinaryCode n) (hD : SelfDual D) :
    2*Module.finrank (ZMod 2) D=n := by
  let B := dotBilinear (n:=n)
  have he : B.orthogonal D=D := by
    ext x
    change (∀ y,y∈D → dot y x=0) ↔ x∈D
    rw [hD x]
    simp only [dot_comm]
  have hd := LinearMap.BilinForm.finrank_orthogonal (B:=B) dotBilinear_nondegenerate D
  rw [he] at hd
  have hn : Module.finrank (ZMod 2) (BinaryVector n)=n := by simp [BinaryVector]
  rw [hn] at hd
  have hle : Module.finrank (ZMod 2) D≤n := by simpa only [hn] using Submodule.finrank_le D
  omega

 theorem flat_support_selfDual (f : Signature ℂ n) (hf : Flat f)
    (a : BinaryVector n) (D : BinaryCode n)
    (hs : ∀ x,f (wordVector x)≠0 ↔ x-a∈D) :
    SelfDual D := by
  obtain ⟨c,b,E,hE,he⟩ := hf
  have hh : ∀ x,f (wordVector x)≠0 ↔ x-b∈E := by
    intro x
    rw [he]
    have hb : (fun i => bit (wordVector x i))=x := by
      exact vector_word x
    have hb' : (fun i => bit (wordVector x i)-b i)=x-b := by
      funext i
      exact congrArg (fun t => t-b i) (congrFun hb i)
    simp only [flatSignature,hb']
    split_ifs with hx
    · rw [hb'] at hx
      simp [hx,c.ne_zero]
    · rw [hb'] at hx
      simp [hx]
  have eq := affine_support_direction_unique (fun x => f (wordVector x)) a b D E hs hh
  rw [eq]
  exact hE


 theorem flat_support_dimension (f : Signature ℂ n) (hf : Flat f)
    (a : BinaryVector n) (D : BinaryCode n)
    (hs : ∀ x,f (wordVector x)≠0 ↔ x-a∈D) :
    2*Module.finrank (ZMod 2) D=n :=
  selfDual_half_dimension D (flat_support_selfDual f hf a D hs)

end
end Holant.ReedMuller.AffineRadon
