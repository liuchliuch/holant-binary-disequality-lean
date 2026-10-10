import Holant.Dihedral.SupportIntegration.GlobalProjection

/-! The equal-coordinate projection has exactly the residual matching code
as its image. Actual global lifts are constructed from the local patch. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
open Holant.Dihedral.CompatibleClosure
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

 theorem LocalPatch.equal_lift {F : BinaryVector (n+2) → K} {o : Equiv.Perm (Fin (n+2))}
    (D : LocalPatch F o) (y : BinaryVector n) (hy : y ∈ (Pairing.ofPorts D.ports).code) :
    ∃ x : BinaryVector (n+2),x ∈ D.code ∧ x 0=x 1 ∧ (fun i => x i.succ.succ)=y := by
  rw [←D.matching_extension,mem_extension] at hy
  rcases hy with hy|hy
  · refine ⟨Fin.cons 0 (Fin.cons 0 y),?_,rfl,rfl⟩
    change (fun i => y i+0*(D.a+D.c) i+0*(D.a+D.b) i) ∈ D.L
    simpa only [zero_mul,add_zero] using hy
  · refine ⟨Fin.cons 1 (Fin.cons 1 y),?_,rfl,rfl⟩
    change (fun i => y i+1*(D.a+D.c) i+1*(D.a+D.b) i) ∈ D.L
    have he : (fun i => y i+1*(D.a+D.c) i+1*(D.a+D.b) i)=y+(D.b+D.c) := by
      funext i
      simp only [one_mul,Pi.add_apply]
      have hh : y i+(D.a i+D.c i)+(D.a i+D.b i)=y i+(D.b i+D.c i)+(D.a i+D.a i) := by abel
      rw [hh,ZModModule.add_self,add_zero]
    rw [he]
    exact hy

 def ExactMatchingProjections {N : ℕ} (D : BinaryCode N) : Prop :=
  ∀ i j : Fin N,i ≠ j → ∃ r : ℕ,∃ p : (Fin r × Bool) ≃ Remaining i j,
    ∀ y : Remaining i j → ZMod 2,
      (∃ x : BinaryVector N,x ∈ D ∧ x i=x j ∧ ∀ k : Remaining i j,x k.val=y k) ↔
        ∀ e,y (p (e,false))=y (p (e,true))

 theorem LocalAtlas.exactMatchingProjections {F : BinaryVector (n+2) → K} (A : LocalAtlas F) :
    ExactMatchingProjections A.direction := by
  intro i j hij
  let o := pairOrder i j
  let D := A.patch o
  let R := Holant.Dihedral.TwoCardLocalization.remainingOrder i j hij
  let p := D.ports.trans R
  refine ⟨D.edges,p,?_⟩
  intro y
  constructor
  · rintro ⟨x,hx,he,hrest⟩ e
    have hn : pull o x ∈ D.code := by rw [A.direction_at o] at hx; exact hx
    have hxy : pull o x 0=pull o x 1 := by
      simpa only [pull_apply,o,pairOrder_first i j hij,pairOrder_second] using he
    have hp := (Pairing.ofPorts_code D.ports _).mp (D.equal_projection (pull o x) hn hxy) e
    change x (p (e,false)).val=x (p (e,true)).val at hp
    simpa only [hrest] using hp
  · intro hy
    have hres : (fun k : Fin n => y (R k)) ∈ (Pairing.ofPorts D.ports).code := by
      rw [Pairing.ofPorts_code]
      intro e
      exact hy e
    obtain ⟨z,hz,hzEq,hzRest⟩ := D.equal_lift _ hres
    let x := pull o.symm z
    have hx : x ∈ A.direction := by
      rw [A.direction_at o]
      change pull o (pull o.symm z) ∈ D.code
      rw [pull_pull_symm]
      exact hz
    have hxi : x i=z 0 := by
      change z (o.symm i)=z 0
      have hh := pairOrder_first i j hij
      change o 0=i at hh
      rw [←hh,Equiv.symm_apply_apply]
    have hxj : x j=z 1 := by
      change z (o.symm j)=z 1
      have hh := pairOrder_second i j
      change o 1=j at hh
      rw [←hh,Equiv.symm_apply_apply]
    refine ⟨x,hx,hxi.trans (hzEq.trans hxj.symm),?_⟩
    intro k
    obtain ⟨l,rfl⟩ := R.surjective k
    change z (o.symm (o l.succ.succ))=y (R l)
    rw [Equiv.symm_apply_apply]
    exact congrFun hzRest l

end Holant.Dihedral.SupportIntegration
