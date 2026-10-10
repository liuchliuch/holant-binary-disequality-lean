import Holant.Dihedral.EndpointSaturation.Source

/-! Construct the global affine direction from four literal endpoint cosets
and their parallelogram. No global code or self-duality is assumed. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def globalCode (L : BinaryCode n) (u v : BinaryVector n) : BinaryCode (n+2) where
  carrier := {x | (fun i => x i.succ.succ+x 0*u i+x 1*v i) ∈ L}
  zero_mem' := by
    change (fun i : Fin n => (0:ZMod 2)+0*u i+0*v i) ∈ L
    simp only [zero_mul,zero_add]
    exact L.zero_mem
  add_mem' := by
    intro x y hx hy
    have he : (fun i => (x+y) i.succ.succ+(x+y) 0*u i+(x+y) 1*v i)=
        (fun i => x i.succ.succ+x 0*u i+x 1*v i)+(fun i => y i.succ.succ+y 0*u i+y 1*v i) := by
      funext i
      simp only [Pi.add_apply]
      ring
    change (fun i => (x+y) i.succ.succ+(x+y) 0*u i+(x+y) 1*v i) ∈ L
    rw [he]
    exact L.add_mem hx hy
  smul_mem' := by
    intro c x hx
    have he : (fun i => (c • x) i.succ.succ+(c • x) 0*u i+(c • x) 1*v i)=
        c • (fun i => x i.succ.succ+x 0*u i+x 1*v i) := by
      funext i
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    change (fun i => (c • x) i.succ.succ+(c • x) 0*u i+(c • x) 1*v i) ∈ L
    rw [he]
    exact L.smul_mem c hx

 def globalOffset (a : BinaryVector n) : BinaryVector (n+2) := Fin.cons 0 (Fin.cons 0 a)

 theorem global_coset_join (L : BinaryCode n) (u v a : BinaryVector n)
    (b c : ZMod 2) (x : BinaryVector n) :
    Fin.cons b (Fin.cons c x) ∈ coset (globalCode L u v) (globalOffset a) ↔
      x+a+b • u+c • v ∈ L := by
  change (fun i => ((Fin.cons b (Fin.cons c x) : BinaryVector (n+2))+globalOffset a) i.succ.succ+
    ((Fin.cons b (Fin.cons c x) : BinaryVector (n+2))+globalOffset a) 0*u i+
    ((Fin.cons b (Fin.cons c x) : BinaryVector (n+2))+globalOffset a) 1*v i) ∈ L ↔ _
  simp only [globalOffset,Pi.add_apply,Fin.cons_zero,Fin.cons_succ,Fin.cons_one,add_zero]
  rfl

 private theorem add_translate_iff (L : BinaryCode n) (x y : BinaryVector n) (hy : y ∈ L) :
    x+y ∈ L ↔ x ∈ L := by
  constructor
  · intro hh
    have he := L.add_mem hh hy
    simpa [add_assoc,ZModModule.add_self] using he
  · intro hx
    exact L.add_mem hx hy

/-- The source's displayed affine code is constructed from the four endpoint
cosets. Their parallelogram is the exact compatibility condition for the11
slice. The theorem allows arbitrary nonzero coefficients on those cosets. -/
 theorem four_cosets_global {K : Type*} [Field K] (F : BinaryVector (n+2) → K)
    (L : BinaryCode n) (a b c d : BinaryVector n)
    (h00 : fullCoset (fun x => F (Fin.cons 0 (Fin.cons 0 x))) L a)
    (h01 : fullCoset (fun x => F (Fin.cons 0 (Fin.cons 1 x))) L b)
    (h10 : fullCoset (fun x => F (Fin.cons 1 (Fin.cons 0 x))) L c)
    (h11 : fullCoset (fun x => F (Fin.cons 1 (Fin.cons 1 x))) L d)
    (hpar : a+b+c+d ∈ L) :
    fullCoset F (globalCode L (a+c) (a+b)) (globalOffset a) := by
  intro x
  have hx : Fin.cons (x 0) (Fin.cons (x 1) (fun i => x i.succ.succ))=x := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  have hjoin (z w : ZMod 2) (y : BinaryVector n) :
      F (Fin.cons z (Fin.cons w y)) ≠ 0 ↔
        Fin.cons z (Fin.cons w y) ∈ coset (globalCode L (a+c) (a+b)) (globalOffset a) := by
    rw [global_coset_join]
    have hz : z=0 ∨ z=1 := by fin_cases z; exact Or.inl rfl; exact Or.inr rfl
    have hw : w=0 ∨ w=1 := by fin_cases w; exact Or.inl rfl; exact Or.inr rfl
    rcases hz with rfl|rfl <;> rcases hw with rfl|rfl
    · simpa only [zero_smul,add_zero] using (show F (Fin.cons 0 (Fin.cons 0 y)) ≠ 0 ↔ y+a ∈ L from h00 y)
    · have he : y+a+(a+b)=y+b := ZModModule.add_add_add_cancel _ _ _
      simpa only [zero_smul,one_smul,add_zero,he] using (show F (Fin.cons 0 (Fin.cons 1 y)) ≠ 0 ↔ y+b ∈ L from h01 y)
    · have he : y+a+(a+c)=y+c := ZModModule.add_add_add_cancel _ _ _
      simpa only [zero_smul,one_smul,add_zero,he] using (show F (Fin.cons 1 (Fin.cons 0 y)) ≠ 0 ↔ y+c ∈ L from h10 y)
    · simp only [one_smul]
      have he : y+a+(a+c)+(a+b)=(y+d)+(a+b+c+d) := by
        rw [show y+a+(a+c)+(a+b)=y+(a+b+c) by
          have hh : y+a+(a+c)+(a+b)=y+(a+a)+(a+b+c) := by abel
          rw [hh,ZModModule.add_self,add_zero]]
        have hh : (y+d)+(a+b+c+d)=(y+(a+b+c))+(d+d) := by abel
        rw [hh,ZModModule.add_self,add_zero]
      rw [he,add_translate_iff L _ _ hpar]
      exact h11 y
  simpa only [hx] using hjoin (x 0) (x 1) (fun i => x i.succ.succ)

end Holant.Dihedral.SupportIntegration
