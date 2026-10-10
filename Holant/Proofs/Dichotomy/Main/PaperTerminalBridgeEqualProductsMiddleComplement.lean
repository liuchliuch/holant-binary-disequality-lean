import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsMiddleNormalize
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeComplementSign

/-! Signed middle normalization gives one common complement sign. The
existing actual negative-sign cap construction removes it, preserving the
old field, all old family rows and every physical multiplier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMiddleComplement
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
namespace N
export PaperTerminalBridgeEqualProductsMiddleNormalize (sign sign_sq Signed source)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

theorem sign_product (s x : Fin 4→Bool) :
    N.sign (K:=K) s x=∏i : Fin 4,if s i && x i then (-1:K) else 1 := by
  unfold N.sign
  rw [←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases s i && x i <;> simp

theorem sign_complement_product (s x : Fin 4→Bool) :
    N.sign (K:=K) s x*N.sign s (fun i=> !(x i))=N.sign s (fun _=>true) := by
  simp only [sign_product]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> cases x i <;> simp

theorem sign_complement (s x : Fin 4→Bool) :
    N.sign (K:=K) s x=N.sign s (fun _=>true)*N.sign s (fun i=> !(x i)) := by
  rw [←sign_complement_product s x,mul_assoc,←pow_two,N.sign_sq,mul_one]

theorem common (q : Signature K 4) (signed : N.Signed q) :
    ∃ε : K,ε^2=1 ∧ (entries q).b=ε*(entries q).y ∧
      (entries q).c=ε*(entries q).z ∧ (entries q).d=ε*(entries q).w := by
  obtain ⟨c,_live,s,form⟩ := signed
  let ε : K:=N.sign s (fun _=>true)
  have pairs (x : Fin 4→Bool) (middle : weight x=2) : q x=ε*q (fun i=> !(x i)) := by
    have other : weight (fun i=> !(x i))=2 := by
      have h:=Holant.weight_compl_add x
      rw [middle] at h
      omega
    rw [form x middle,form _ other,sign_complement s x]
    change c*(ε*N.sign s (fun i=> !(x i)))=ε*(c*N.sign s (fun i=> !(x i)))
    ring
  have b : (fun i : Fin 4=> !(![false,false,true,true] i))=![true,true,false,false] := by
    funext i;fin_cases i <;> rfl
  have z : (fun i : Fin 4=> !(![false,true,false,true] i))=![true,false,true,false] := by
    funext i;fin_cases i <;> rfl
  have w : (fun i : Fin 4=> !(![false,true,true,false] i))=![true,false,false,true] := by
    funext i;fin_cases i <;> rfl
  refine ⟨ε,N.sign_sq s _,?_,?_,?_⟩
  · simpa only [entries,b] using pairs ![false,false,true,true] (by decide)
  · simpa only [entries,z] using pairs ![false,true,false,true] (by decide)
  · simpa only [entries,w] using pairs ![false,true,true,false] (by decide)

variable [CharZero K]
theorem source (phi : K→+*AlgebraicComplex) (F : SignatureFamily K) (q : Signature K 4)
    (actual : Gadget.Realizes F .disequality q) (even : EvenSupport q)
    (dense : StableDenseParityAlgebra.Dense q) (products : PaperTerminalBridgeEqualProductsMiddle.Products q) :
    ∃g : Signature K 4,Gadget.RealizesUpTo F .disequality g ∧ EvenSupport g ∧
      StableDenseParityAlgebra.Dense g ∧ PaperTerminalBridgeComplementSign.Complement g := by
  obtain ⟨g,actualG,evenG,denseG,signed⟩ := N.source phi F q actual even dense products
  obtain ⟨ε,square,b,c,d⟩ := common g signed
  exact PaperTerminalBridgeComplementSign.source F g actualG evenG denseG ε square b c d


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMiddleComplement
end
