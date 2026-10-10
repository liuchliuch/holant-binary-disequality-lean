import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramNorm
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMBell

/-! Exact unnormalized Bell coordinates of a real six-port source.
Second-order orthogonality forces the four actual Bell cards to be nonzero,
mutually orthogonal and of the same norm, with the literal factor two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixBellNorm
open Holant
namespace E
export GlobalCloseCompletionKleinH6RMBell (E bell)
end E
namespace W
export GlobalCloseCompletionKleinGramCertificate (word)
end W
namespace N
export GlobalCloseCompletionKleinGramNorm (rows OrthogonalPair)
end N
namespace A
export GlobalCloseCompletionKleinGramAnalysis (gram)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def matrix (k i : Fin 4) : ℝ := E.E k (W.word i 0) (W.word i 1)

theorem matrix_orthogonal (k l : Fin 4) :
    (∑i : Fin 4,matrix k i*matrix l i)=if k=l then 2 else 0 := by
  fin_cases k <;> fin_cases l <;> norm_num [matrix,E.E,E.bell,W.word,Fin.sum_univ_succ]

def card (f : Signature ℝ 6) (k : Fin 4) : Signature ℝ 4 :=
  fun z=>∑i : Fin 4,matrix k i*N.rows (n:=4) f i z

theorem gram_linear {ι : Type*} [Fintype ι] (f : Fin 4→ι→ℝ) (a b : Fin 4→ℝ) :
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

theorem card_gram (f : Signature ℝ 6) (d : ℝ)
    (orthogonal : ∀u v : Fin 2→Bool,
      (∑z : Fin 4→Bool,f (Fin.addCases (m:=2) (n:=4) u z)*f (Fin.addCases (m:=2) (n:=4) v z))=if u=v then d else 0)
    (k l : Fin 4) :
    (∑z : Fin 4→Bool,card f k z*card f l z)=if k=l then 2*d else 0 := by
  have rows (i j : Fin 4) : (∑z : Fin 4→Bool,N.rows (n:=4) f i z*N.rows (n:=4) f j z)=
      if i=j then d else 0 := by
    have h := orthogonal (W.word i) (W.word j)
    have words : W.word i=W.word j ↔ i=j := GlobalCloseCompletionKleinGramNorm.wordEquiv.injective.eq_iff
    simpa only [N.rows,words] using h
  simp only [card]
  rw [gram_linear]
  simp only [rows,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [←Finset.sum_mul,matrix_orthogonal]
  split_ifs <;> ring

theorem orthogonal_cards (f : Signature ℝ 6) (orthogonal : N.OrthogonalPair (n:=4) f) :
    ∃d : ℝ,0<d ∧ (∀k l,(∑z : Fin 4→Bool,card f k z*card f l z)=if k=l then 2*d else 0) ∧
      ∀k,card f k≠0 := by
  obtain ⟨d,positive,equation⟩ := orthogonal
  refine ⟨d,positive,card_gram f d equation,?_⟩
  intro k zero
  have h := card_gram f d equation k k
  simp only [zero,Pi.zero_apply,mul_zero,Finset.sum_const_zero,ite_true] at h
  linarith

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixBellNorm
end
