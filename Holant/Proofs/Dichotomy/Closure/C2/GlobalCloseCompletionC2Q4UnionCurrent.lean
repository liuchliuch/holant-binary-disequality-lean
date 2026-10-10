import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SafeSymmetry

/-! Every small checker row is an exact ordered current I/X contraction.
The eight coefficients retain the proven simultaneous-complement symmetry;
no parity or transformed resource is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4UnionCurrent
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Pauli.ExoticKlein.SixPort
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open GlobalCloseCompletionC2TensorMatching
open scoped QuadraticAlgebra
namespace U
export GlobalCloseCompletionC2Q4Union (Safe Holds cardRows)
end U
namespace I
export GlobalCloseCompletionC2SparseInteger (toIRow toIRows value)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option Elab.async false

def word : Fin 8→(Fin 4→Bool) := ![![false,false,false,false],![true,false,false,false],![false,true,false,false],![true,true,false,false],![false,false,true,false],![true,false,true,false],![false,true,true,false],![true,true,true,false]]
def coefficients (f : Signature ℂ 4) : Fin 8→ℂ := fun i=>f (word i)
def tensor {K : Type*} (v : Fin 8→K) : Signature K 4 := fun x=>match x 0,x 1,x 2,x 3 with
  | false,false,false,false => v 0
  | false,false,false,true => v 7
  | false,false,true,false => v 4
  | false,false,true,true => v 3
  | false,true,false,false => v 2
  | false,true,false,true => v 5
  | false,true,true,false => v 6
  | false,true,true,true => v 1
  | true,false,false,false => v 1
  | true,false,false,true => v 6
  | true,false,true,false => v 5
  | true,false,true,true => v 2
  | true,true,false,false => v 3
  | true,true,false,true => v 4
  | true,true,true,false => v 7
  | true,true,true,true => v 0

theorem tensor_coefficients (f : Signature ℂ 4) (comp : ∀x,f x=f (fun i=>!(x i))) : tensor (coefficients f)=f := by
  have eta (x : Fin 4→Bool) : ![x 0,x 1,x 2,x 3]=x := by funext i;fin_cases i <;> rfl
  have cv (b c d e : Bool) : f ![!b,!c,!d,!e]=f ![b,c,d,e] := by
    have h := comp ![b,c,d,e]
    convert h.symm using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  funext x
  rw [←eta x]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [tensor,coefficients,word,h0,h1,h2,h3]
  · exact cv false false false true
  · exact cv false false true true
  · exact cv false true false true
  · exact cv false true true true
  · exact cv true false false true
  · exact cv true false true true
  · exact cv true true false true
  · simpa using cv true true true true

def order (c : Fin 12) : Equiv.Perm (Fin 4) where
  toFun := (![![0,1,2,3],![0,1,2,3],![0,2,1,3],![0,2,1,3],![0,3,1,2],![0,3,1,2],![1,2,0,3],![1,2,0,3],![1,3,0,2],![1,3,0,2],![2,3,0,1],![2,3,0,1]] : Fin 12→Fin 4→Fin 4) c
  invFun := (![![0,1,2,3],![0,1,2,3],![0,2,1,3],![0,2,1,3],![0,2,3,1],![0,2,3,1],![2,0,1,3],![2,0,1,3],![2,0,3,1],![2,0,3,1],![2,3,0,1],![2,3,0,1]] : Fin 12→Fin 4→Fin 4) c
  left_inv := by fin_cases c <;> decide
  right_inv := by fin_cases c <;> decide

def phase (c : Fin 12) : Bool := c.val % 2=1

theorem literal_binary (f : Signature ℂ 2) (h : LiteralMatching f) : f ![false,false]=0 ∨ f ![false,true]=0 := by
  rcases h with rfl|⟨k,ports,label,c,hc,rfl⟩
  · exact Or.inl rfl
  have size := Fintype.card_congr ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at size
  have hk : k=1 := by omega
  subst k
  have distinct : ports (0,false)≠ports (0,true) := by intro h;have e:=ports.injective h;cases e
  cases hp : label 0
  · right
    generalize h0 : ports (0,false)=a at *
    generalize h1 : ports (0,true)=b at *
    fin_cases a <;> fin_cases b
    all_goals simp_all [productValue,Fin.prod_univ_succ,originalC2Binary,Matrix.one_apply]
  · left
    generalize h0 : ports (0,false)=a at *
    generalize h1 : ports (0,true)=b at *
    fin_cases a <;> fin_cases b
    all_goals simp_all [productValue,Fin.prod_univ_succ,originalC2Binary,X,Signature.disequality]

theorem card_evaluate (v : Fin 8→ℂ) (c : Fin 12) (t : Bool) :
    LinearCertificate.evaluate (IntegerCertificate.mapRow (I.toIRow (U.cardRows c t))) v=
      Signature.contract (originalC2Binary (phase c)) (Tensor.reindex (order c).symm (tensor v)) ![false,t] := by
  fin_cases c <;> cases t
  all_goals norm_num [LinearCertificate.evaluate,IntegerCertificate.mapRow,I.toIRow,I.value,U.cardRows,
    Fin.sum_univ_succ,Signature.contract,originalC2Binary,phase,order,Tensor.reindex,tensor,X,Matrix.one_apply,Signature.disequality]
  all_goals ring

theorem safe_coefficients (f : Signature ℂ 4) (comp : ∀x,f x=f (fun i=>!(x i)))
    (safe : GlobalCloseCompletionC2SafeSymmetry.Safe f) : U.Safe (coefficients f) := by
  intro c
  have h := literal_binary _ (safe (order c) (phase c))
  rcases h with h|h
  · refine ⟨false,?_⟩
    intro row member
    have eqn : row=IntegerCertificate.mapRow (I.toIRow (U.cardRows c false)) := by
      simpa only [IntegerCertificate.mapRows,I.toIRows,List.map_cons,List.map_nil,List.mem_singleton] using member
    rw [eqn,card_evaluate,tensor_coefficients f comp]
    exact h
  · refine ⟨true,?_⟩
    intro row member
    have eqn : row=IntegerCertificate.mapRow (I.toIRow (U.cardRows c true)) := by
      simpa only [IntegerCertificate.mapRows,I.toIRows,List.map_cons,List.map_nil,List.mem_singleton] using member
    rw [eqn,card_evaluate,tensor_coefficients f comp]
    exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4UnionCurrent
end
