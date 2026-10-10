import Holant.Platonic.StabilizerLine.Source
import Mathlib.FieldTheory.Finiteness

/-! Off-origin supports obtained with one common Clifford normalization. -/
namespace Holant.Platonic.ActiveSupport
open Holant Holant.Platonic.StabilizerLine
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def offSupport (f : Signature ℂ n) : Finset (BinaryVector n) :=
  Finset.univ.filter (fun x => x≠0 ∧ f (wordVector x)≠0)

@[simp] theorem mem_offSupport (f : Signature ℂ n) (x : BinaryVector n) :
    x∈offSupport f ↔ x≠0 ∧ f (wordVector x)≠0 := by simp [offSupport]

theorem offSupport_scale (f : Signature ℂ n) (c : ℂ) (hc : c≠0) :
    offSupport (fun x => c*f x)=offSupport f := by
  ext x
  simp [hc]

theorem offSupport_zero : offSupport (0 : Signature ℂ n)=∅ := by
  ext x
  simp

theorem offSupport_scaled_delta (c : ℂ) :
    offSupport (fun x : Fin n → Bool => c*delta x)=∅ := by
  ext x
  simp only [mem_offSupport,delta_vector,Finset.notMem_empty,iff_false]
  rintro ⟨hx,hh⟩
  simp [hx] at hh

theorem code_card_le_four (D : BinaryCode n) (hD : Module.finrank (ZMod 2) D≤2) :
    Fintype.card D≤4 := by
  rw [Module.card_eq_pow_finrank (K:=ZMod 2) (V:=D),ZMod.card]
  exact (Nat.pow_le_pow_right (by norm_num : 1≤2) hD).trans (by norm_num)

theorem offSupport_card_le_three {f : Signature ℂ n} (h : SharpSupport f) :
    (offSupport f).card≤3 := by
  rcases h with ⟨a,ha,hs⟩|⟨D,hD,hs⟩
  · have he : offSupport f={a} := by
      ext x
      simp only [mem_offSupport,hs,Finset.mem_singleton]
      exact ⟨fun hx => hx.2,fun hx => ⟨hx ▸ ha,hx⟩⟩
    rw [he]
    simp
  · let T : Finset (BinaryVector n) := Finset.univ.filter (fun x => x∈D)
    have he : offSupport f=T.erase 0 := by
      ext x
      simp [T,hs]
    have hT : T.card=Fintype.card D := by
      simp [T,Fintype.card_subtype]
    have h0 : (0 : BinaryVector n)∈T := by simp [T]
    rw [he,Finset.card_erase_of_mem h0,hT]
    have hh := code_card_le_four D hD
    omega

theorem offSupport_three_sum_zero {f : Signature ℂ n} (h : SharpSupport f)
    (hc : (offSupport f).card=3) : ∑x∈offSupport f,x=0 := by
  rcases h with ⟨a,ha,hs⟩|⟨D,hD,hs⟩
  · have hsub : offSupport f⊆{a} := by
      intro x hx
      exact Finset.mem_singleton.mpr ((hs x).mp ((mem_offSupport f x).mp hx).2)
    have hh := Finset.card_le_card hsub
    simp [hc] at hh
  · obtain ⟨x,y,z,hxy,hxz,hyz,he⟩ := Finset.card_eq_three.mp hc
    have hm (t : BinaryVector n) : t∈offSupport f ↔ t≠0 ∧ t∈D := by
      simp only [mem_offSupport,hs]
    have hx : x≠0 ∧ x∈D := (hm x).mp (by simp [he])
    have hy : y≠0 ∧ y∈D := (hm y).mp (by simp [he])
    have hsum0 : x+y≠0 := by
      intro hh
      apply hxy
      have hh' := congrArg (fun t => t+y) hh
      simpa [add_assoc,binary_self] using hh'
    have hsumx : x+y≠x := by
      intro hh
      apply hy.1
      exact add_left_cancel (hh.trans (add_zero x).symm)
    have hsumy : x+y≠y := by
      intro hh
      apply hx.1
      exact add_right_cancel (hh.trans (zero_add y).symm)
    have hmxy : x+y∈offSupport f := (hm _).mpr ⟨hsum0,D.add_mem hx.2 hy.2⟩
    have hez : x+y=z := by simpa [he,hsumx,hsumy] using hmxy
    rw [he]
    rw [Finset.sum_insert (by simp [hxy,hxz]),
      Finset.sum_insert (by simp [hyz]),Finset.sum_singleton,←hez]
    simpa [add_assoc,binary_self] using binary_self (x+y)

/-- The sharp line theorem can use any already chosen common normalization.
Zero intermediate line values are explicitly included in the empty-support case. -/
theorem normalized_offSupport_shape (u v : Signature ℂ n)
    (α : ℂ) (hα : α≠0) (hu : u=fun x => α*delta x)
    (hv : ComplexAffine v) (c : ℂ) (hc : c≠0)
    (hw : ComplexAffine (fun x => u x+c*v x)) :
    (offSupport v).card≤3 ∧
      ((offSupport v).card=3 → ∑x∈offSupport v,x=0) := by
  by_cases hv0 : v=0
  · simp [hv0,offSupport_zero]
  by_cases hw0 : (fun x => u x+c*v x)=0
  · have he : v=fun x => (-c⁻¹*α)*delta x := by
      funext x
      have hh := congrFun hw0 x
      rw [hu] at hh
      dsimp at hh
      field_simp
      linear_combination hh
    rw [he,offSupport_scaled_delta]
    simp
  let w : Signature ℂ n := fun x => α⁻¹*v x
  have hw' : ComplexAffine (fun x => delta x+c*w x) := by
    have hh := hw.scale α⁻¹
    convert hh using 1
    funext x
    rw [hu]
    dsimp [w]
    field_simp
  have hw0' : (fun x => delta x+c*w x)≠0 := by
    intro hh
    apply hw0
    funext x
    have he := congrFun hh x
    rw [hu]
    dsimp [w] at he ⊢
    field_simp at he
    linear_combination he
  have hv0' : w≠0 := by
    intro hh
    apply hv0
    funext x
    have he := congrFun hh x
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hα)
  have hs : SharpSupport v := (SharpSupport.scale_iff v α⁻¹ (inv_ne_zero hα)).mp
    (normalized_sharp_support w (hv.scale α⁻¹) hv0' c hc hw' hw0')
  exact ⟨offSupport_card_le_three hs,offSupport_three_sum_zero hs⟩

end
end Holant.Platonic.ActiveSupport
