import Holant.Dihedral.SupportIntegration.LocalData
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The global direction has half the ambient dimension. Both dimensions
are calculated from explicit linear coordinates, not assumed. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ}

 def matchingCoordinates (p : (Fin r × Bool) ≃ Fin n) :
    (Pairing.ofPorts p).code ≃ₗ[ZMod 2] (Fin r → ZMod 2) where
  toFun x e := x.val (p (e,false))
  invFun y := ⟨fun i => y (p.symm i).1,by
    rw [Pairing.ofPorts_code]
    intro e
    simp⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    obtain ⟨⟨e,b⟩,rfl⟩ := p.surjective i
    cases b
    · simp
    · simpa using (Pairing.ofPorts_code p x.val).mp x.property e
  right_inv y := by funext e; simp
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

 theorem matching_finrank (p : (Fin r × Bool) ≃ Fin n) :
    Module.finrank (ZMod 2) (Pairing.ofPorts p).code=r := by
  simpa using (matchingCoordinates p).finrank_eq

 def assemble (u v : BinaryVector n) (z : BinaryVector n × (ZMod 2 × ZMod 2)) : BinaryVector (n+2) :=
  Fin.cons z.2.1 (Fin.cons z.2.2 (fun i => z.1 i-z.2.1*u i-z.2.2*v i))

 theorem assemble_mem (L : BinaryCode n) (u v : BinaryVector n)
    (l : L) (a b : ZMod 2) : assemble u v (l.val,(a,b)) ∈ globalCode L u v := by
  change (fun i => assemble u v (l.val,(a,b)) i.succ.succ+
    assemble u v (l.val,(a,b)) 0*u i+assemble u v (l.val,(a,b)) 1*v i) ∈ L
  have hh : (fun i => assemble u v (l.val,(a,b)) i.succ.succ+
      assemble u v (l.val,(a,b)) 0*u i+assemble u v (l.val,(a,b)) 1*v i)=l.val := by
    funext i
    simp only [assemble,Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
    ring
  rw [hh]
  exact l.property

 def globalCoordinates (L : BinaryCode n) (u v : BinaryVector n) :
    globalCode L u v ≃ₗ[ZMod 2] (L × (ZMod 2 × ZMod 2)) where
  toFun x := (⟨fun i => x.val i.succ.succ+x.val 0*u i+x.val 1*v i,x.property⟩,(x.val 0,x.val 1))
  invFun z := ⟨assemble u v (z.1.val,z.2),assemble_mem L u v z.1 z.2.1 z.2.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · change x.val k.succ.succ+x.val 0*u k+x.val 1*v k-x.val 0*u k-x.val 1*v k=x.val k.succ.succ
      ring
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp only [assemble,Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
      ring
    · rfl
  map_add' := by
    intro x y
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change (x.val+y.val) i.succ.succ+(x.val+y.val) 0*u i+(x.val+y.val) 1*v i=
        (x.val i.succ.succ+x.val 0*u i+x.val 1*v i)+(y.val i.succ.succ+y.val 0*u i+y.val 1*v i)
      simp only [Pi.add_apply]
      ring
    · rfl
  map_smul' := by
    intro c x
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change (c • x.val) i.succ.succ+(c • x.val) 0*u i+(c • x.val) 1*v i=
        c*(x.val i.succ.succ+x.val 0*u i+x.val 1*v i)
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    · rfl

 theorem globalCode_finrank (L : BinaryCode n) (u v : BinaryVector n) :
    Module.finrank (ZMod 2) (globalCode L u v)=Module.finrank (ZMod 2) L+2 := by
  have hh := (globalCoordinates L u v).finrank_eq
  simpa using hh

 variable {K : Type*} [Field K]
 theorem LocalPatch.half_dimension {F : BinaryVector (n+2) → K} {o : Equiv.Perm (Fin (n+2))}
    (D : LocalPatch F o) : 2*Module.finrank (ZMod 2) D.code=n+2 := by
  have hm := matching_finrank D.ports
  have he := Submodule.finrank_sup_span_singleton D.odd_outside
  change Module.finrank (ZMod 2) (extension D.L (D.b+D.c))=Module.finrank (ZMod 2) D.L+1 at he
  rw [D.matching_extension,hm] at he
  have hg := globalCode_finrank D.L (D.a+D.c) (D.a+D.b)
  change Module.finrank (ZMod 2) D.code=Module.finrank (ZMod 2) D.L+2 at hg
  have hn := Fintype.card_congr D.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hn
  omega

 theorem LocalAtlas.half_dimension {F : BinaryVector (n+2) → K} (A : LocalAtlas F) :
    2*Module.finrank (ZMod 2) A.direction=n+2 := by
  have he : A.direction=(A.patch (Equiv.refl _)).code := by ext x; rfl
  rw [he]
  exact (A.patch (Equiv.refl _)).half_dimension

 theorem LocalPatch.pair_lift {F : BinaryVector (n+2) → K} {o : Equiv.Perm (Fin (n+2))}
    (D : LocalPatch F o) (a b : ZMod 2) :
    ∃ x : BinaryVector (n+2),x ∈ D.code ∧ x 0=a ∧ x 1=b := by
  exact ⟨assemble (D.a+D.c) (D.a+D.b) (0,(a,b)),
    assemble_mem D.L _ _ 0 a b,rfl,rfl⟩

 theorem LocalAtlas.pair_lift {F : BinaryVector (n+2) → K} (A : LocalAtlas F)
    (i j : Fin (n+2)) (hij : i ≠ j) (a b : ZMod 2) :
    ∃ x : BinaryVector (n+2),x ∈ A.direction ∧ x i=a ∧ x j=b := by
  let o := Holant.Dihedral.CompatibleClosure.pairOrder i j
  obtain ⟨z,hz,h0,h1⟩ := (A.patch o).pair_lift a b
  refine ⟨pull o.symm z,?_,?_,?_⟩
  · rw [A.direction_at o]
    change pull o (pull o.symm z) ∈ (A.patch o).code
    rw [pull_pull_symm]
    exact hz
  · change z (o.symm i)=a
    have hi := Holant.Dihedral.CompatibleClosure.pairOrder_first i j hij
    change o 0=i at hi
    rw [←hi,Equiv.symm_apply_apply]
    exact h0
  · change z (o.symm j)=b
    have hj := Holant.Dihedral.CompatibleClosure.pairOrder_second i j
    change o 1=j at hj
    rw [←hj,Equiv.symm_apply_apply]
    exact h1

end Holant.Dihedral.SupportIntegration
