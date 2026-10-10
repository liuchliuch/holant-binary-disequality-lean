import Holant.Platonic.StabilizerLine.Cube

/-! The sharp normalized stabilizer-line bound. The support alternative is
proved from the two literal affine tensors, without a support-size premise. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def delta : Signature ℂ n := fun x => if x=origin n then 1 else 0

@[simp] theorem delta_vector (x : BinaryVector n) :
    delta (wordVector x)=(if x=0 then 1 else 0) := by
  have h : wordVector x=origin n ↔ x=0 := by
    constructor
    · intro h;simpa using congrArg vectorWord h
    · intro h;subst x;rfl
  simp only [delta,h]

def SharpSupport (f : Signature ℂ n) : Prop :=
  (∃ a : BinaryVector n,a≠0 ∧ ∀ x,f (wordVector x)≠0 ↔ x=a) ∨
  (∃ D : BinaryCode n,Module.finrank (ZMod 2) D≤2 ∧ ∀ x,f (wordVector x)≠0 ↔ x∈D)

theorem normalized_sharp_support (v : Signature ℂ n) (hv : ComplexAffine v) (hn : v≠0)
    (c : ℂ) (hc : c≠0)
    (hw : ComplexAffine (fun x => delta x+c*v x))
    (hwn : (fun x => delta x+c*v x)≠0) : SharpSupport v := by
  obtain ⟨A⟩ := hv.normalForm hn
  obtain ⟨B⟩ := hw.normalForm hwn
  let w : Signature ℂ n := fun x => delta x+c*v x
  have he (x : BinaryVector n) : w (wordVector x)=(if x=0 then 1 else 0)+c*v (wordVector x) := by
    simp only [w,delta_vector]
  have hoff (x : BinaryVector n) (hx : x≠0) :
      w (wordVector x)≠0 ↔ v (wordVector x)≠0 := by
    rw [he,if_neg hx,zero_add]
    exact mul_ne_zero_iff.trans (and_iff_right hc)
  by_cases h0 : v (wordVector 0)=0
  · left
    have ha : v (wordVector A.shift)≠0 := (A.support _).mpr (by simp)
    have han : A.shift≠0 := by intro h;exact ha (h ▸ h0)
    refine ⟨A.shift,han,?_⟩
    intro x
    constructor
    · intro hx
      by_contra hxa
      have hxn : x≠0 := by intro h;exact hx (h ▸ h0)
      have hxan : x+A.shift≠0 := by
        intro h
        have hh := congrArg (fun t => t+A.shift) h
        apply hxa
        simpa [add_assoc,binary_self] using hh
      have hw0 : w (wordVector 0)≠0 := by rw [he,if_pos rfl,h0];norm_num
      have hsum := B.ternary 0 x A.shift hw0 ((hoff x hxn).mpr hx) ((hoff _ han).mpr ha)
      have hvsum : v (wordVector (x+A.shift))≠0 := (hoff _ hxan).mp (by simpa only [zero_add] using hsum)
      have hh := A.ternary x A.shift (x+A.shift) hx ha hvsum
      exact hh (by rw [binary_self];exact h0)
    · intro h;simpa [h] using ha
  · right
    refine ⟨A.direction,?_,A.support_linear h0⟩
    by_contra hd
    have hd' : 3≤Module.finrank (ZMod 2) A.direction := by omega
    obtain ⟨E,hE,hm⟩ := exists_cube_embedding A.direction hd'
    apply delta_cube_impossible A B c hc he E hE
    intro x
    exact (A.support_linear h0 _).mpr (hm x)

end
end Holant.Platonic.StabilizerLine
