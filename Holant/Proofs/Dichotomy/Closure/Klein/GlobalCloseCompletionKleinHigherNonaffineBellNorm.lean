import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineMatching
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramNorm

/-! Exact standard-Pauli product norms and Bell coefficients over the complex
field. A real Gram source can be transported to this statement with its actual
normalization scalar; equal coefficient squares are then a conclusion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
namespace Matching

theorem square_sum {P : Type*} [Fintype P] [DecidableEq P] {r : ℕ}
    (M : Matching P r) (labels : Fin r→Label) :
    (∑x,M.tensor labels x^2)=(2:ℂ)^r := by
  rw [M.sum_assignments]
  simp only [tensor_coordinates,←Finset.prod_pow]
  rw [←Fintype.prod_sum (fun (i : Fin r) (p : Bool×Bool)=>E (labels i) p.1 p.2^2)]
  have localNorm (i : Fin r) : (∑p : Bool×Bool,E (labels i) p.1 p.2^2)=(2:ℂ) := by
    have h := gram (labels i) (labels i)
    simpa only [Kernel.pair,Fintype.sum_prod_type,pow_two,theta,d,dOver,ite_true,mul_one] using h
  simp_rw [localNorm]
  simp

end Matching
namespace BellNorm
open Holant.Dihedral.CompatibleCoefficientLine (pair)
namespace W
export GlobalCloseCompletionKleinGramCertificate (word)
end W
namespace N
export GlobalCloseCompletionKleinGramNorm (wordEquiv)
end N

def matrix (a : Label) (i : Fin 4) : ℂ := dual a (W.word i 0) (W.word i 1)

theorem matrix_orthogonal (a b : Label) :
    (∑i : Fin 4,matrix a i*matrix b i)=if a=b then (1/2:ℂ) else 0 := by
  rcases label_cases a with rfl|rfl|rfl|rfl <;>
    rcases label_cases b with rfl|rfl|rfl|rfl <;>
    norm_num [matrix,dual,dualOver,dOver,theta,EOver,W.word,Fin.sum_univ_succ,
      xLabel,yLabel,zLabel,label_zero,Prod.mk.injEq] <;> decide

theorem contract_rows {n : ℕ} (f : Signature ℂ (n+2)) (a : Label) (z : Fin n→Bool) :
    Signature.contract (n:=n) (dual a) f z=∑i : Fin 4,matrix a i*f (pair (W.word i 0) (W.word i 1) z) := by
  simp [Signature.contract,Fintype.sum_bool,Fin.sum_univ_succ,matrix,W.word,pair]
  ring


 theorem gram_linear {ι : Type*} [Fintype ι] (f : Fin 4→ι→ℂ) (a b : Fin 4→ℂ) :
    (∑z,(∑i,a i*f i z)*(∑j,b j*f j z))=
      ∑i : Fin 4,∑j : Fin 4,a i*b j*(∑z,f i z*f j z) := by
  have point (z : ι) : (∑i,a i*f i z)*(∑j,b j*f j z)=
      ∑i : Fin 4,∑j : Fin 4,a i*b j*(f i z*f j z) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [point]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

theorem card_gram {n : ℕ} (f : Signature ℂ (n+2)) (d : ℂ)
    (orthogonal : ∀u v : Fin 2→Bool,
      (∑z : Fin n→Bool,f (pair (u 0) (u 1) z)*f (pair (v 0) (v 1) z))=if u=v then d else 0)
    (a b : Label) :
    (∑z : Fin n→Bool,Signature.contract (n:=n) (dual a) f z*
      Signature.contract (n:=n) (dual b) f z)=if a=b then d/2 else 0 := by
  have rows (i j : Fin 4) : (∑z : Fin n→Bool,f (pair (W.word i 0) (W.word i 1) z)*f (pair (W.word j 0) (W.word j 1) z))=
      if i=j then d else 0 := by
    have h := orthogonal (W.word i) (W.word j)
    have words : W.word i=W.word j ↔ i=j := N.wordEquiv.injective.eq_iff
    simpa only [words] using h
  simp_rw [contract_rows]
  rw [gram_linear]
  simp only [rows,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [←Finset.sum_mul,matrix_orthogonal]
  split_ifs <;> ring

theorem coefficient_squares {n r : ℕ} (f : Signature ℂ (n+2)) (d : ℂ)
    (orthogonal : ∀u v : Fin 2→Bool,
      (∑z : Fin n→Bool,f (pair (u 0) (u 1) z)*f (pair (v 0) (v 1) z))=if u=v then d else 0)
    (M : Matching (Fin n) r) (weight : Label→ℂ) (labels : Label→Fin r→Label)
    (form : ∀a,Signature.contract (n:=n) (dual a) f=fun z=>weight a*M.tensor (labels a) z) :
    ∀a,weight a^2=weight 0^2 := by
  have norm (a : Label) : weight a^2*(2:ℂ)^r=d/2 := by
    have h := card_gram f d orthogonal a a
    simp only [ite_true,form,←pow_two,mul_pow] at h
    rw [←Finset.mul_sum,Matching.square_sum] at h
    exact h
  intro a
  exact mul_right_cancel₀ (pow_ne_zero r (by norm_num : (2:ℂ)≠0)) ((norm a).trans (norm 0).symm)

end BellNorm
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
end
