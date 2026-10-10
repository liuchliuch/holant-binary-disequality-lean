import Holant.Platonic.ActiveSupport.Source
import Mathlib.FieldTheory.Finiteness

/-! The literal supported Hilbert space and its commuting Z-Pauli description.
This is the concrete stabilizer-code interpretation of the active-support bound. -/
namespace Holant.Platonic.StabilizerCode
noncomputable section
open Holant Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.RadonAccess
open Holant.Platonic.StabilizerLine
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def supportedSpace (D : BinaryCode n) : Submodule ℂ (Signature ℂ n) where
  carrier := {f | ∀w,vectorWord w∉D → f w=0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg w hw;simp [hf w hw,hg w hw]
  smul_mem' := by intro c f hf w hw;simp [hf w hw]

@[simp] theorem mem_supportedSpace (D : BinaryCode n) (f : Signature ℂ n) :
    f∈supportedSpace D ↔ ∀w,vectorWord w∉D → f w=0 := Iff.rfl

 def supportedEquiv (D : BinaryCode n) : supportedSpace D ≃ₗ[ℂ] (D→ℂ) where
  toFun f x := f.val (wordVector x.val)
  invFun g := ⟨fun w=>if h : vectorWord w∈D then g ⟨vectorWord w,h⟩ else 0,
    by intro w hw;simp [hw]⟩
  left_inv f := by
    apply Subtype.ext
    funext w
    by_cases hw : vectorWord w∈D
    · simp [hw]
    · simp [hw,f.property w hw]
  right_inv g := by
    funext x
    simp
  map_add' f g := rfl
  map_smul' c f := rfl

 theorem supportedSpace_finrank (D : BinaryCode n) :
    Module.finrank ℂ (supportedSpace D)=2^Module.finrank (ZMod 2) D := by
  rw [(supportedEquiv D).finrank_eq,Module.finrank_pi]
  simpa using (Module.card_eq_pow_finrank (K:=ZMod 2) (V:=D))

 def dualCode (D : BinaryCode n) : BinaryCode n := (dotBilinear (n:=n)).orthogonal D

 theorem mem_code_iff_dual (D : BinaryCode n) (x : BinaryVector n) :
    x∈D ↔ ∀z∈dualCode D,dot z x=0 := by
  have hs : (dotBilinear (n:=n)).IsSymm := ⟨dot_comm⟩
  have he := (dotBilinear (n:=n)).orthogonal_orthogonal dotBilinear_nondegenerate hs.isRefl D
  change x∈D ↔ x∈(dotBilinear (n:=n)).orthogonal ((dotBilinear (n:=n)).orthogonal D)
  rw [he]

 def zAction (z : BinaryVector n) : Signature ℂ n →ₗ[ℂ] Signature ℂ n where
  toFun f w := sign (dot z (vectorWord w))*f w
  map_add' f g := by ext w;simp [mul_add]
  map_smul' c f := by ext w;simp [mul_left_comm]

 theorem zAction_standard (z : BinaryVector n) (f : Signature ℂ n) :
    zAction z f=standardPauli 0 0 z f := by
  ext w
  rw [standardPauli_dot]
  simp [zAction]

 theorem zAction_add (z t : BinaryVector n) (f : Signature ℂ n) :
    zAction (z+t) f=zAction z (zAction t f) := by
  ext w
  simp [zAction,dot_add_left,sign_add,mul_assoc]

@[simp] theorem zAction_zero (f : Signature ℂ n) : zAction 0 f=f := by
  ext w
  simp [zAction,Holant.ReedMuller.LowArity.dot]

 theorem zAction_commute (z t : BinaryVector n) (f : Signature ℂ n) :
    zAction z (zAction t f)=zAction t (zAction z f) := by
  rw [←zAction_add,←zAction_add,add_comm z t]

 theorem supported_iff_z_fixed (D : BinaryCode n) (f : Signature ℂ n) :
    f∈supportedSpace D ↔ ∀z∈dualCode D,zAction z f=f := by
  constructor
  · intro hf z hz
    ext w
    by_cases hw : vectorWord w∈D
    · have hd := (mem_code_iff_dual D (vectorWord w)).mp hw z hz
      simp [zAction,hd]
    · simp [zAction,hf w hw]
  · intro hf w hw
    by_contra hn
    apply hw
    apply (mem_code_iff_dual D (vectorWord w)).mpr
    intro z hz
    have he := congrFun (hf z hz) w
    change sign (dot z (vectorWord w))*f w=f w at he
    rcases binary_cases (dot z (vectorWord w)) with hd|hd
    · exact hd
    · rw [hd,sign_one] at he
      have h0 : f w=0 := by linear_combination (-he)/2
      exact (hn h0).elim

end
end Holant.Platonic.StabilizerCode
