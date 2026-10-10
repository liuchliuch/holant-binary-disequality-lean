import Holant.Dihedral.EndpointSaturation.Code

/-! Canonical endpoint offsets and exact affine supports. The offset fixes the
selected edge and all other matching equations retain their original parity. -/
noncomputable section
namespace Holant.Dihedral.EndpointSaturation
open Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {r n : ℕ}

 def endpointOffset (p : (Fin r × Bool) ≃ Fin n) (e : Fin r)
    (α : Fin r → ZMod 2) (a b : ZMod 2) : BinaryVector n := fun i =>
  if (p.symm i).1=e then (if (p.symm i).2 then b else a)
    else (if (p.symm i).2 then α (p.symm i).1 else 0)

 private theorem add_zero_iff (a b : ZMod 2) : a+b=0 ↔ a=b := by
  rw [←ZModModule.sub_eq_add,sub_eq_zero]
 private theorem add_switch (a b c : ZMod 2) : a=b+c ↔ b=a+c := by
  constructor
  · intro h
    have hh := congrArg (·+c) h
    simpa [add_assoc,ZModModule.add_self] using hh.symm
  · intro h
    have hh := congrArg (·+c) h
    simpa [add_assoc,ZModModule.add_self] using hh.symm

 theorem fixed_coset_iff (p : (Fin r × Bool) ≃ Fin n) (e : Fin r)
    (α : Fin r → ZMod 2) (a b : ZMod 2) (x : BinaryVector n) :
    x ∈ coset (fixedCode p e) (endpointOffset p e α a b) ↔
      x (p (e,false))=a ∧ x (p (e,true))=b ∧
      ∀ j,j ≠ e → x (p (j,true))=x (p (j,false))+α j := by
  change ((x+endpointOffset p e α a b) ∈ (Pairing.ofPorts p).code ∧
    (x+endpointOffset p e α a b) (p (e,false))=0) ↔ _
  rw [Pairing.ofPorts_code]
  simp only [Pi.add_apply,endpointOffset,Equiv.symm_apply_apply,ite_true,Bool.false_eq_true,ite_false]
  constructor
  · rintro ⟨hm,hzero⟩
    have hx := (add_zero_iff _ _).mp hzero
    have he := hm e
    simp only [ite_true] at he
    have hy : x (p (e,true))=b := (add_zero_iff _ _).mp (he.symm.trans hzero)
    refine ⟨hx,hy,?_⟩
    intro j hj
    have hh := hm j
    simp only [hj,ite_false,add_zero] at hh
    exact (add_switch _ _ _).mp hh
  · rintro ⟨hx,hy,hrest⟩
    refine ⟨?_,(add_zero_iff _ _).mpr hx⟩
    intro j
    by_cases hj : j=e
    · subst j
      simp [hx,hy,ZModModule.add_self]
    · simp only [hj,ite_false,add_zero]
      exact (add_switch _ _ _).mpr (hrest j hj)

 theorem complementary_offsets (p : (Fin r × Bool) ≃ Fin n) (e : Fin r)
    (α : Fin r → ZMod 2) (a b : ZMod 2) :
    endpointOffset p e α a b+endpointOffset p e α (a+1) (b+1)=edgeVector p e := by
  funext i
  by_cases he : (p.symm i).1=e <;> cases hb : (p.symm i).2 <;>
    simp [endpointOffset,edgeVector,he,hb,←add_assoc,ZModModule.add_self]

 theorem complementary_extensions (p : (Fin r × Bool) ≃ Fin n) (e : Fin r)
    (α : Fin r → ZMod 2) (a b c d : ZMod 2) :
    let x₀ := endpointOffset p e α a b
    let x₁ := endpointOffset p e α (a+1) (b+1)
    let y₀ := endpointOffset p e α c d
    let y₁ := endpointOffset p e α (c+1) (d+1)
    x₀+x₁ ∉ fixedCode p e ∧ y₀+y₁ ∉ fixedCode p e ∧
    extension (fixedCode p e) (x₀+x₁)=(Pairing.ofPorts p).code ∧
    extension (fixedCode p e) (y₀+y₁)=(Pairing.ofPorts p).code ∧
    x₀+y₀+y₁+x₁ ∈ fixedCode p e ∧ SelfDual (Pairing.ofPorts p).code := by
  dsimp only
  have he := complementary_offsets p e α a b
  have ho := complementary_offsets p e α c d
  refine ⟨?_,?_,?_,?_,?_,pairing_code_selfDual p⟩
  · rw [he]; exact edgeVector_not_fixed p e
  · rw [ho]; exact edgeVector_not_fixed p e
  · rw [he]; exact extension_fixedCode p e
  · rw [ho]; exact extension_fixedCode p e
  · have hh : endpointOffset p e α a b+endpointOffset p e α c d+
        endpointOffset p e α (c+1) (d+1)+endpointOffset p e α (a+1) (b+1)=
        (endpointOffset p e α a b+endpointOffset p e α (a+1) (b+1))+
        (endpointOffset p e α c d+endpointOffset p e α (c+1) (d+1)) := by abel
    rw [hh,he,ho,ZModModule.add_self]
    exact (fixedCode p e).zero_mem

end Holant.Dihedral.EndpointSaturation
