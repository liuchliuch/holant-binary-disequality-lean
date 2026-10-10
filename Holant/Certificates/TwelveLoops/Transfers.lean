import Holant.Certificates.TwelveLoops.Gaussian
import Holant.Certificates.TwelveLoops.Contraction
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Bool

/-! Actual binary ranks and projective powers for the loop coefficient pairs.
Projective finite order here means a positive matrix power is a nonzero scalar
identity, not a predicate with an assumed connection to the transfer matrix. -/
noncomputable section
namespace Holant.Certificates.TwelveLoops

def transfer (P Q : Gaussian) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun j => if j then embed Q else embed P)

def offMatrix (P Q : Gaussian) : Matrix Bool Bool ℂ :=
  (transfer P Q).submatrix (Equiv.refl Bool) Equiv.boolNot

def flip : Matrix Bool Bool ℂ := fun i j => if i≠j then 1 else 0

theorem off_mul_flip (P Q : Gaussian) : offMatrix P Q * flip = transfer P Q := by
  ext i j
  cases i <;> cases j <;> simp [offMatrix,transfer,flip,Matrix.mul_apply,Matrix.submatrix,Equiv.boolNot]

theorem diagonal_support_flip (P Q : Gaussian) : transfer P Q * flip * (1 : Matrix Bool Bool ℂ) = offMatrix P Q := by
  ext i j
  cases i <;> cases j <;> simp [offMatrix,transfer,flip,Matrix.mul_apply,Matrix.submatrix,Equiv.boolNot]

theorem rankOneTest_rank (P Q : Gaussian) (h : rankOneTest (P,Q)=true) :
    (transfer P Q).rank=1 ∧ (offMatrix P Q).rank=1 := by
  classical
  have hd : (transfer P Q).rank=1 := by
    rw [transfer,Matrix.rank_diagonal,Fintype.card_subtype]
    by_cases hP : P=(0,0) <;> by_cases hQ : Q=(0,0)
    all_goals simp [rankOneTest,hP,hQ] at h
    all_goals simp [Finset.filter_insert,Finset.filter_singleton,embed_zero_iff,hP,hQ]
  exact ⟨hd,(Matrix.rank_submatrix _ _ _).trans hd⟩

def ProjectivelyFinite (M : Matrix Bool Bool ℂ) : Prop :=
  ∃ n : ℕ, n≠0 ∧ ∃ c : ℂ, c≠0 ∧ M^n=c • (1 : Matrix Bool Bool ℂ)

theorem transfer_power_ratio (P Q : Gaussian) (hQ : Q≠(0,0))
    (h : ProjectivelyFinite (transfer P Q)) : gnorm P=gnorm Q := by
  obtain ⟨n,hn,c,hc,hm⟩ := h
  have hp := congrArg (fun M : Matrix Bool Bool ℂ => M false false) hm
  have hq := congrArg (fun M : Matrix Bool Bool ℂ => M true true) hm
  simp [transfer,Matrix.diagonal_pow] at hp hq
  apply torsion_implies_norm P Q hQ n hn
  rw [div_pow,hp,hq,div_self hc]

theorem norm_mismatch_infinite (P Q : Gaussian) (h : infiniteTest (P,Q)=true) :
    ¬ ProjectivelyFinite (transfer P Q) := by
  have hh : P≠(0,0) ∧ Q≠(0,0) ∧ gnorm P≠gnorm Q := by
    simpa [infiniteTest,and_assoc] using h
  exact fun hf => hh.2.2 (transfer_power_ratio P Q hh.2.1 hf)

theorem transfer_finite_of_fourth_root (P Q : Gaussian) (hQ : Q≠(0,0))
    (h : (embed P/embed Q)^4=1) : ProjectivelyFinite (transfer P Q) := by
  have hn : embed Q≠0 := (not_congr (embed_zero_iff Q)).mpr hQ
  have hp : embed P^4=embed Q^4 := by
    rw [div_pow,div_eq_one_iff_eq (pow_ne_zero _ hn)] at h
    exact h
  refine ⟨4,by decide,embed Q^4,pow_ne_zero _ hn,?_⟩
  ext i j
  cases i <;> cases j <;> simp [transfer,Matrix.diagonal_pow,hp]

theorem loopPairs_are_sums (s : State) (p : Gaussian × Gaussian) (hp : p∈loopPairs s) :
    ∃ i j k l : Fin 4, p=(gadd (fourthRoot i) (fourthRoot j),gadd (fourthRoot k) (fourthRoot l)) := by
  simp only [loopPairs,List.mem_append,List.mem_ofFn] at hp
  rcases hp with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · exact ⟨alpha s (pairs r).1,alpha s (pairs r).2,beta s (pairs r).1,beta s (pairs r).2,rfl⟩
  · exact ⟨alpha s (complements r).2,beta s (complements r).1,
      alpha s (complements r).1,beta s (complements r).2,rfl⟩

theorem remaining_fourth_root (s : State) (hs : classify s=.remaining)
    (p : Gaussian × Gaussian) (hp : p∈loopPairs s) :
    (p.1=(0,0) ∧ p.2=(0,0)) ∨
    (p.1≠(0,0) ∧ p.2≠(0,0) ∧ (embed p.1/embed p.2)^4=1) := by
  have hh := (remaining_iff s).mp hs
  by_cases hP : p.1=(0,0)
  · exact Or.inl ⟨hP,(hh.1 p hp).mp hP⟩
  · have hQ : p.2≠(0,0) := fun h => hP ((hh.1 p hp).mpr h)
    refine Or.inr ⟨hP,hQ,?_⟩
    obtain ⟨i,j,k,l,rfl⟩ := loopPairs_are_sums s p hp
    exact (fourth_root_iff_equal_norm i j k l hP hQ).mpr (hh.2 _ hp hP hQ)

theorem native_loop_matrix (s : State) (p : Fin 6) :
    (fun x y : Bool => loopAt (fun j => embed (a s j)) (fun j => embed (b s j)) p true ![x,y]) =
      transfer (nativePair s p).1 (nativePair s p).2 := by
  ext x y
  rw [native_loop_formula]
  cases x <;> cases y <;> simp [nativePair,diagonal,transfer,embed_add]

theorem equality_loop_matrix (s : State) (p : Fin 6) :
    (fun x y : Bool => equalityMediatedLoop (fun j => embed (a s j)) (fun j => embed (b s j)) p ![x,y]) =
      offMatrix (equalityPair s p).1 (equalityPair s p).2 := by
  ext x y
  rw [equality_mediated_formula]
  cases x <;> cases y <;>
    simp [equalityPair,antidiagonal,offMatrix,transfer,embed_add,Matrix.submatrix,Equiv.boolNot]

end Holant.Certificates.TwelveLoops
