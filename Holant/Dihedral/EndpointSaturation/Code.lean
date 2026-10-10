import Holant.Dihedral.EndpointParallelogram.Factors
import Holant.ReedMuller.LowArity.Basic

/-! Fixed-edge matching directions and their exact self-dual one-edge
extensions. These are literal submodules on the original residual ports. -/
noncomputable section
namespace Holant.Dihedral.EndpointSaturation
open Holant.Dihedral.EndpointParallelogram
open Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {r n : ℕ}

 def fixedCode (p : (Fin r × Bool) ≃ Fin n) (e : Fin r) : BinaryCode n where
  carrier := {x | x ∈ (Pairing.ofPorts p).code ∧ x (p (e,false))=0}
  zero_mem' := ⟨(Pairing.ofPorts p).code.zero_mem,rfl⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨(Pairing.ofPorts p).code.add_mem hx.1 hy.1,by simp only [Pi.add_apply,hx.2,hy.2,add_zero]⟩
  smul_mem' := by
    intro c x hx
    exact ⟨(Pairing.ofPorts p).code.smul_mem c hx.1,by simp only [Pi.smul_apply,hx.2,smul_zero]⟩

 def edgeVector (p : (Fin r × Bool) ≃ Fin n) (e : Fin r) : BinaryVector n :=
  fun i => if (p.symm i).1=e then 1 else 0

 theorem edgeVector_mem (p : (Fin r × Bool) ≃ Fin n) (e : Fin r) :
    edgeVector p e ∈ (Pairing.ofPorts p).code := by
  rw [Pairing.ofPorts_code]
  intro j
  simp [edgeVector]

 theorem edgeVector_not_fixed (p : (Fin r × Bool) ≃ Fin n) (e : Fin r) :
    edgeVector p e ∉ fixedCode p e := by
  intro hh
  have he := hh.2
  simp [edgeVector] at he

 theorem extension_fixedCode (p : (Fin r × Bool) ≃ Fin n) (e : Fin r) :
    extension (fixedCode p e) (edgeVector p e)=(Pairing.ofPorts p).code := by
  ext x
  rw [mem_extension]
  constructor
  · rintro (hx|hx)
    · exact hx.1
    · have hh := (Pairing.ofPorts p).code.add_mem hx.1 (edgeVector_mem p e)
      simpa [add_assoc,ZModModule.add_self] using hh
  · intro hx
    by_cases hzero : x (p (e,false))=0
    · exact Or.inl ⟨hx,hzero⟩
    · right
      refine ⟨(Pairing.ofPorts p).code.add_mem hx (edgeVector_mem p e),?_⟩
      have hone : x (p (e,false))=1 := by
        generalize hh : x (p (e,false))=b at *
        fin_cases b <;> simp_all
      simp [edgeVector,hone,ZModModule.add_self]

 theorem pairing_code_selfDual (p : (Fin r × Bool) ≃ Fin n) :
    SelfDual (Pairing.ofPorts p).code := by
  intro x
  constructor
  · intro hx y hy
    have hxp := (Pairing.ofPorts_code p x).mp hx
    have hyp := (Pairing.ofPorts_code p y).mp hy
    unfold dot
    rw [←p.sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro e _
    simp only [Fintype.sum_bool,hxp e,hyp e,ZModModule.add_self]
  · intro hx
    rw [Pairing.ofPorts_code]
    intro e
    have hh := hx (edgeVector p e) (edgeVector_mem p e)
    unfold dot at hh
    rw [←p.sum_comp,Fintype.sum_prod_type] at hh
    have hs : (∑ j : Fin r,∑ b : Bool,x (p (j,b))*edgeVector p e (p (j,b)))=
        x (p (e,false))+x (p (e,true)) := by
      simp [edgeVector,Fintype.sum_bool,add_comm]
    rw [hs] at hh
    have he := congrArg (·+x (p (e,true))) hh
    simpa [add_assoc,ZModModule.add_self] using he

end Holant.Dihedral.EndpointSaturation
