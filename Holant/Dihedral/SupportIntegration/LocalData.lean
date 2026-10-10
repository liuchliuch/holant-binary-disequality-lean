import Holant.Dihedral.SupportIntegration.Reindex
import Holant.Dihedral.SupportIntegration.Projection
import Holant.Dihedral.CompatibleClosure.PairOrder

/-! A weaker local support interface for the global-code argument. It contains
four endpoint cosets and their parallelogram, and one residual matching
extension; it does not require a fixed-edge C/C coefficient presentation. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

 structure LocalPatch (F : BinaryVector (n+2) → K) (o : Equiv.Perm (Fin (n+2))) where
  L : BinaryCode n
  a : BinaryVector n
  b : BinaryVector n
  c : BinaryVector n
  d : BinaryVector n
  full00 : fullCoset (fun x => F (pull o.symm (Fin.cons 0 (Fin.cons 0 x)))) L a
  full01 : fullCoset (fun x => F (pull o.symm (Fin.cons 0 (Fin.cons 1 x)))) L b
  full10 : fullCoset (fun x => F (pull o.symm (Fin.cons 1 (Fin.cons 0 x)))) L c
  full11 : fullCoset (fun x => F (pull o.symm (Fin.cons 1 (Fin.cons 1 x)))) L d
  parallelogram : a+b+c+d ∈ L
  odd_outside : b+c ∉ L
  edges : ℕ
  ports : (Fin edges × Bool) ≃ Fin n
  matching_extension : extension L (b+c)=(Pairing.ofPorts ports).code

 def LocalPatch.code {F : BinaryVector (n+2) → K} {o : Equiv.Perm (Fin (n+2))}
    (D : LocalPatch F o) : BinaryCode (n+2) := globalCode D.L (D.a+D.c) (D.a+D.b)

 theorem LocalPatch.full_normalized {F : BinaryVector (n+2) → K} {o : Equiv.Perm (Fin (n+2))}
    (D : LocalPatch F o) : fullCoset (fun x => F (pull o.symm x)) D.code (globalOffset D.a) :=
  four_cosets_global _ D.L D.a D.b D.c D.d D.full00 D.full01 D.full10 D.full11 D.parallelogram

 theorem LocalPatch.full_original {F : BinaryVector (n+2) → K} {o : Equiv.Perm (Fin (n+2))}
    (D : LocalPatch F o) : fullCoset F (reindexCode o D.code) (pull o.symm (globalOffset D.a)) :=
  fullCoset_reindex F o D.code _ D.full_normalized

 theorem LocalPatch.equal_projection {F : BinaryVector (n+2) → K} {o : Equiv.Perm (Fin (n+2))}
    (D : LocalPatch F o) (x : BinaryVector (n+2)) (hx : x ∈ D.code) (heq : x 0=x 1) :
    (fun i => x i.succ.succ) ∈ (Pairing.ofPorts D.ports).code := by
  rw [←D.matching_extension,mem_extension]
  change (fun i => x i.succ.succ+x 0*(D.a+D.c) i+x 1*(D.a+D.b) i) ∈ D.L at hx
  have hz : x 0=0 ∨ x 0=1 := by
    generalize hh : x 0=z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  have huv : (D.a+D.c)+(D.a+D.b)=D.b+D.c := by
    calc
      _=(D.a+D.a)+(D.b+D.c) := by abel
      _=D.b+D.c := by rw [ZModModule.add_self,zero_add]
  rcases hz with hz|hz
  · left
    simpa only [←heq,hz,zero_mul,add_zero] using hx
  · right
    have hh : (fun i => x i.succ.succ+(D.a+D.c) i+(D.a+D.b) i)=
        (fun i => x i.succ.succ)+(D.b+D.c) := by
      funext i
      have h := congrFun huv i
      change (D.a+D.c) i+(D.a+D.b) i=(D.b+D.c) i at h
      simp only [Pi.add_apply] at h ⊢
      simpa only [add_assoc] using congrArg (fun z => x i.succ.succ+z) h
    simpa only [←heq,hz,one_mul,hh] using hx

/-- Local patches can be supplied by any independent support argument. This
record contains no global direction or self-duality witness. -/
 structure LocalAtlas (F : BinaryVector (n+2) → K) where
  patch : ∀ o : Equiv.Perm (Fin (n+2)),LocalPatch F o

 def LocalAtlas.direction {F : BinaryVector (n+2) → K} (A : LocalAtlas F) : BinaryCode (n+2) :=
  reindexCode (Equiv.refl _) (A.patch (Equiv.refl _)).code
 def LocalAtlas.offset {F : BinaryVector (n+2) → K} (A : LocalAtlas F) : BinaryVector (n+2) :=
  globalOffset (A.patch (Equiv.refl _)).a

 theorem LocalAtlas.full_support {F : BinaryVector (n+2) → K} (A : LocalAtlas F) :
    fullCoset F A.direction A.offset := by
  have hh := (A.patch (Equiv.refl _)).full_original
  exact hh

 theorem LocalAtlas.direction_at {F : BinaryVector (n+2) → K} (A : LocalAtlas F)
    (o : Equiv.Perm (Fin (n+2))) : A.direction=reindexCode o (A.patch o).code :=
  fullCoset_direction_unique F _ _ _ _ A.full_support (A.patch o).full_original

end Holant.Dihedral.SupportIntegration
