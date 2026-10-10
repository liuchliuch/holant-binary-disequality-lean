import Holant.ReedMuller.SupportReconstruction.GlobalCode
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The reconstructed support has exactly half the ambient dimension. A
literal supported nonconstant word makes an equal-pair functional surjective;
its kernel is one of the already derived parity-lift slice codes. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant.ReedMuller.LowArity Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.FlatNetwork
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def pairLinear (i j : Fin n) : BinaryVector n →ₗ[ZMod 2] ZMod 2 where
   toFun x := x i+x j
   map_add' := by intro x y; simp [Pi.add_apply]; ring
   map_smul' := by intro c x; simp [Pi.smul_apply,smul_eq_mul]; ring
 @[simp] theorem pairLinear_apply (i j : Fin n) (x : BinaryVector n) : pairLinear i j x=x i+x j := rfl

 theorem mem_pair_ker (i j : Fin n) (x : BinaryVector n) : x∈(pairLinear i j).ker ↔ x i=x j := by
   change x i+x j=0 ↔ x i=x j
   exact (by decide : ∀a b : ZMod 2,a+b=0 ↔ a=b) _ _

 theorem pair_ker_finrank (i j : Fin n) (hij : i≠j) :
     1+Module.finrank (ZMod 2) (pairLinear i j).ker=n := by
   have hs : Function.Surjective (pairLinear i j) := by
     intro c
     refine ⟨Pi.single i c,?_⟩
     simp [pairLinear_apply,Pi.single_apply,Ne.symm hij]
   have he := (pairLinear i j).finrank_range_add_finrank_ker
   rw [LinearMap.range_eq_top.mpr hs] at he
   simpa using he

 theorem sup_pair_ker (D : BinaryCode n) (i j : Fin n) (w : BinaryVector n)
     (hw : w∈D) (hval : pairLinear i j w=1) : D⊔(pairLinear i j).ker=⊤ := by
   apply top_unique
   intro x _
   let d := pairLinear i j x • w
   have hd : d∈D := D.smul_mem _ hw
   have hz : x+d∈(pairLinear i j).ker := by
     change pairLinear i j (x+d)=0
     rw [map_add]
     change pairLinear i j x+pairLinear i j (pairLinear i j x • w)=0
     rw [map_smul,hval]
     simp only [smul_eq_mul,mul_one,add_self_zero]
   refine Submodule.mem_sup.mpr ⟨d,hd,x+d,hz,?_⟩
   calc
     d+(x+d)=x+(d+d) := by abel
     _=x := by rw [ZModModule.add_self,add_zero]

 namespace LocalSlices
 variable {S : Set (BinaryVector n)} (A : LocalSlices S)
 include A

 theorem exists_nonconstant (hn : 6≤n) :
     ∃w : BinaryVector n,w∈S ∧ ∃a b : Fin n,w a=1 ∧ w b=0 := by
   let i : Fin n := ⟨0,by omega⟩
   let j : Fin n := ⟨1,by omega⟩
   have hij : i≠j := by intro h;have hh:=congrArg Fin.val h;change 0=1 at hh;omega
   obtain ⟨r,p,hp⟩ := A i j hij
   have hr := slice_port_count p hij
   let e : Fin r := ⟨0,by omega⟩
   let d : Fin r := ⟨1,by omega⟩
   have hed : e≠d := by intro h;have hh:=congrArg Fin.val h;change 0=1 at hh;omega
   let w := sliceWord p (Pi.single e 1)
   have hw : w∈sliceCode p := ⟨Pi.single e 1,rfl⟩
   refine ⟨w,((hp w).mpr hw).1,(p (e,false)).val,(p (d,false)).val,?_,?_⟩
   · change sliceWord p (Pi.single e 1) (p (e,false)).val=1
     rw [sliceWord_port]
     simp
   · change sliceWord p (Pi.single e 1) (p (d,false)).val=0
     rw [sliceWord_port]
     simp [Pi.single_apply,hed]

 theorem half_dimension (hn : 6≤n) : 2*Module.finrank (ZMod 2) (A.globalCode hn)=n := by
   obtain ⟨w,hw,i,j,hi,hj⟩ := A.exists_nonconstant hn
   have hij : i≠j := by intro he;rw [he,hj] at hi;exact zero_ne_one hi
   obtain ⟨r,p,hp⟩ := A i j hij
   have hval : pairLinear i j w=1 := by simp [hi,hj]
   have hs := sup_pair_ker (A.globalCode hn) i j w hw hval
   have heq : sliceCode p=(A.globalCode hn)⊓(pairLinear i j).ker := by
     ext x
     rw [Submodule.mem_inf,mem_pair_ker,A.mem_globalCode]
     exact (hp x).symm
   have hdim := Submodule.finrank_sup_add_finrank_inf_eq (A.globalCode hn) (pairLinear i j).ker
   rw [hs,←heq,sliceCode_finrank] at hdim
   have hker := pair_ker_finrank i j hij
   have hports := slice_port_count p hij
   have htop : Module.finrank (ZMod 2) (⊤ : BinaryCode n)=n := by simp
   rw [htop] at hdim
   omega

 theorem selfDual (hn : 6≤n) : SelfDual (A.globalCode hn) :=
   Holant.ReedMuller.LowArity.selfDual_of_selfOrthogonal_halfDimension (A.globalCode hn)
     (A.selfOrthogonal hn) (A.half_dimension hn)

 end LocalSlices
end Holant.ReedMuller.SupportReconstruction
