import Holant.Proofs.Hardness.AdaptiveEOUnitLocal

/-!
# An internally chosen original-port order for five-supported EO signatures

The support cardinality is measured on the six literal original middle words.
The first zero coefficient chooses an explicit permutation of the original four
ports. Its pullback puts the unique missing word at 0011. In particular the two
adaptive pin coordinates are chosen from opposite bits of that missing word.
This file asserts no free access to the reindexed tensor as a palette label.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.FiveSupportEOOrdering
open Holant
open Holant.LocalDrafts.Hardness.EightVertexNonexception
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

abbrev EOSupport (q : Signature K 4) := DenseEOUnitLocal.EOSupport q

/-- Original words in the fixed order b,c,d,w,z,y. -/
def middleWord : Fin 6 → (Fin 4 → Bool) :=
  ![![false,false,true,true], ![false,true,false,true],
    ![false,true,true,false], ![true,false,false,true],
    ![true,false,true,false], ![true,true,false,false]]

def middleCoeff (q : Signature K 4) (i : Fin 6) : K := q (middleWord i)

def ExactlyFive (q : Signature K 4) : Prop := by
  classical
  exact (Finset.univ.filter (fun i : Fin 6 => middleCoeff q i ≠ 0)).card = 5

/-- The original support test is invariant under any zero-reflecting change
of coefficient field; no order or normalization witness is transported. -/
theorem exactlyFive_congr {L : Type*} [Field L]
    {q : Signature K 4} {r : Signature L 4}
    (h : ∀ x, q x=0 ↔ r x=0) : ExactlyFive q ↔ ExactlyFive r := by
  classical
  have hs : Finset.univ.filter (fun i : Fin 6 => middleCoeff q i≠0) =
      Finset.univ.filter (fun i : Fin 6 => middleCoeff r i≠0) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,middleCoeff]
    exact not_congr (h (middleWord i))
  unfold ExactlyFive
  rw [hs]

/-- An explicit coefficient-only form of the cardinality hypothesis. -/
theorem exactlyFive_iff (q : Signature K 4) : ExactlyFive q ↔
    ((entries q).b=0 ∧ (entries q).c≠0 ∧ (entries q).d≠0 ∧
      (entries q).w≠0 ∧ (entries q).z≠0 ∧ (entries q).y≠0) ∨
    ((entries q).b≠0 ∧ (entries q).c=0 ∧ (entries q).d≠0 ∧
      (entries q).w≠0 ∧ (entries q).z≠0 ∧ (entries q).y≠0) ∨
    ((entries q).b≠0 ∧ (entries q).c≠0 ∧ (entries q).d=0 ∧
      (entries q).w≠0 ∧ (entries q).z≠0 ∧ (entries q).y≠0) ∨
    ((entries q).b≠0 ∧ (entries q).c≠0 ∧ (entries q).d≠0 ∧
      (entries q).w=0 ∧ (entries q).z≠0 ∧ (entries q).y≠0) ∨
    ((entries q).b≠0 ∧ (entries q).c≠0 ∧ (entries q).d≠0 ∧
      (entries q).w≠0 ∧ (entries q).z=0 ∧ (entries q).y≠0) ∨
    ((entries q).b≠0 ∧ (entries q).c≠0 ∧ (entries q).d≠0 ∧
      (entries q).w≠0 ∧ (entries q).z≠0 ∧ (entries q).y=0) := by
  classical
  have hu : (Finset.univ : Finset (Fin 6)) = {0,1,2,3,4,5} := by decide
  by_cases hb : (entries q).b=0 <;>
    by_cases hc : (entries q).c=0 <;>
    by_cases hd : (entries q).d=0 <;>
    by_cases hw : (entries q).w=0 <;>
    by_cases hz : (entries q).z=0 <;>
    by_cases hy : (entries q).y=0 <;>
    simp_all [ExactlyFive,hu,Finset.filter_insert,Finset.filter_singleton,
      middleCoeff,middleWord,entries]

/-- The choice uses q itself, with no witness or certificate argument. -/
def missingIndex (q : Signature K 4) : Fin 6 := by
  classical
  exact if (entries q).b=0 then 0 else if (entries q).c=0 then 1 else
    if (entries q).d=0 then 2 else if (entries q).w=0 then 3 else
    if (entries q).z=0 then 4 else 5

/-- The map sends old positions to new slots. -/
def orderAt (i : Fin 6) : Equiv.Perm (Fin 4) where
  toFun := (![![0,1,2,3], ![0,2,1,3], ![0,2,3,1],
    ![2,0,1,3], ![2,0,3,1], ![2,3,0,1]] : Fin 6 → Fin 4 → Fin 4) i
  invFun := (![![0,1,2,3], ![0,2,1,3], ![0,3,1,2],
    ![1,2,0,3], ![1,3,0,2], ![2,3,0,1]] : Fin 6 → Fin 4 → Fin 4) i
  left_inv := by intro j; fin_cases i <;> fin_cases j <;> rfl
  right_inv := by intro j; fin_cases i <;> fin_cases j <;> rfl

def order (q : Signature K 4) : Equiv.Perm (Fin 4) := orderAt (missingIndex q)

def oriented (q : Signature K 4) : Signature K 4 := Tensor.reindex (order q) q

/-- Original middle indices of the six reindexed middle entries. -/
def middleIndexAt : Fin 6 → Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5], ![1,0,2,3,5,4], ![2,0,1,4,5,3],
    ![3,0,4,1,5,2], ![4,0,3,2,5,1], ![5,1,3,2,4,0]]

theorem reindex_middleCoeff (q : Signature K 4) (i j : Fin 6) :
    middleCoeff (Tensor.reindex (orderAt i) q) j = middleCoeff q (middleIndexAt i j) := by
  fin_cases i <;> fin_cases j <;>
    apply congrArg q <;> funext k <;> fin_cases k <;> rfl

theorem middleIndexAt_zero (i : Fin 6) : middleIndexAt i 0=i := by
  fin_cases i <;> rfl

theorem middleIndexAt_ne (i j : Fin 6) (hj : j≠0) : middleIndexAt i j≠i := by
  fin_cases i <;> fin_cases j <;> simp_all [middleIndexAt]

theorem missing_unique (q : Signature K 4) (hq : ExactlyFive q) :
    middleCoeff q (missingIndex q)=0 ∧
      ∀ j : Fin 6, j≠missingIndex q → middleCoeff q j≠0 := by
  rcases (exactlyFive_iff q).mp hq with h | h | h | h | h | h
  all_goals rcases h with ⟨hb,hc,hd,hw,hz,hy⟩
  all_goals constructor
  all_goals first
    | solve | simp_all [missingIndex,middleCoeff,middleWord,entries]
    | intro j hj; fin_cases j <;> simp_all [missingIndex,middleCoeff,middleWord,entries]

theorem missing_zero (q : Signature K 4) (hq : ExactlyFive q) :
    q (middleWord (missingIndex q))=0 := (missing_unique q hq).1

theorem oriented_b_zero (q : Signature K 4) (hq : ExactlyFive q) :
    (entries (oriented q)).b=0 := by
  change middleCoeff (Tensor.reindex (orderAt (missingIndex q)) q) 0=0
  rw [reindex_middleCoeff,middleIndexAt_zero]
  exact (missing_unique q hq).1

theorem oriented_eo (q : Signature K 4) (hq : EOSupport q) : EOSupport (oriented q) := by
  intro x hx
  apply hq
  have hw : weight (fun i => x (order q i)) = weight x :=
    Equiv.sum_comp (order q) (fun i => if x i then 1 else 0)
  simpa only [hw] using hx

theorem oriented_middle (q : Signature K 4) (hq : ExactlyFive q) :
    AdaptiveEOUnitLocal.NonzeroMiddle (oriented q) := by
  have hn (j : Fin 6) (hj : j≠0) : middleCoeff (oriented q) j≠0 := by
    change middleCoeff (Tensor.reindex (orderAt (missingIndex q)) q) j≠0
    rw [reindex_middleCoeff]
    exact (missing_unique q hq).2 _ (middleIndexAt_ne _ _ hj)
  exact ⟨hn 1 (by decide),hn 3 (by decide),hn 4 (by decide),hn 5 (by decide)⟩

/-- The original coordinate used by the first adaptive pin avoids the missing
word, which is zero here rather than the pin's required one. -/
theorem missingWord_zero_bit (q : Signature K 4) :
    middleWord (missingIndex q) ((order q).symm 0)=false := by
  unfold order
  generalize missingIndex q = i
  fin_cases i <;> rfl

/-- The original coordinate used by the second adaptive pin avoids the missing
word, which is one here rather than the pin's required zero. -/
theorem missingWord_one_bit (q : Signature K 4) :
    middleWord (missingIndex q) ((order q).symm 2)=true := by
  unfold order
  generalize missingIndex q = i
  fin_cases i <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.FiveSupportEOOrdering
