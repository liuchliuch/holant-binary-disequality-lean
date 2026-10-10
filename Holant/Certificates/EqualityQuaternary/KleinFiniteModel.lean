import Holant.Certificates.EqualityQuaternary.KleinFiniteData
import Holant.Certificates.EqualityQuaternary.KleinPhysicalDeck

/-! Definition-level Gaussian card/plane semantics for the finite cover.
Cached matrices become usable only through their separate exact equalities
with cardFormula and targetFormula; no computed table is a source hypothesis.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Linear
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

def inverseIndex : Fin 24 → Fin 24 :=
  ![0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]
def permutation (p : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := permutationData p
  invFun := permutationData (inverseIndex p)
  left_inv := by
    have h : ∀ p i,permutationData (inverseIndex p) (permutationData p i)=i := by decide +kernel
    exact h p
  right_inv := by
    have h : ∀ p i,permutationData p (permutationData (inverseIndex p) i)=i := by decide +kernel
    exact h p
@[simp] theorem permutation_apply (p : Fin 24) (a : Fin 4) : permutation p a=permutationData p a := rfl

theorem permutations_complete : ∀ e : Equiv.Perm (Fin 4),∃ p,permutation p=e := by decide +kernel

def firstLabel (i : Fin 16) : Fin 4 := ⟨i.val/4,by omega⟩
def secondLabel (i : Fin 16) : Fin 4 := ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
def cell (a b : Fin 4) : Fin 16 := ⟨4*a.val+b.val,by omega⟩
def cells : Fin 4 × Fin 4 ≃ Fin 16 where
  toFun := fun ab => cell ab.1 ab.2
  invFun := fun i => (firstLabel i,secondLabel i)
  left_inv := by rintro ⟨a,b⟩; fin_cases a <;> fin_cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem sum_cells {K : Type*} [AddCommMonoid K] (f : Fin 16 → K) :
    (∑ i,f i)=∑ a : Fin 4,∑ b : Fin 4,f (cell a b) := by
  rw [←cells.sum_comp,Fintype.sum_prod_type]
  rfl

def word : Fin 16 → (Fin 4 → Bool) :=
  ![![false,false,false,false],![false,false,false,true],![false,false,true,false],![false,false,true,true],
    ![false,true,false,false],![false,true,false,true],![false,true,true,false],![false,true,true,true],
    ![true,false,false,false],![true,false,false,true],![true,false,true,false],![true,false,true,true],
    ![true,true,false,false],![true,true,false,true],![true,true,true,false],![true,true,true,true]]

theorem words_complete : ∀ w : Fin 4 → Bool,∃ i,word i=w := by decide +kernel

def crossOrder : Fin 4 → Fin 4 → Fin 4 := ![![0,2,1,3],![0,3,1,2],![1,2,0,3],![1,3,0,2]]
def crossInverse : Fin 4 → Fin 4 → Fin 4 := ![![0,2,1,3],![0,2,3,1],![2,0,1,3],![2,0,3,1]]
def crossPermutation (p : Fin 4) : Equiv.Perm (Fin 4) where
  toFun := crossOrder p
  invFun := crossInverse p
  left_inv := by
    have h : ∀ p i,crossInverse p (crossOrder p i)=i := by decide
    exact h p
  right_inv := by
    have h : ∀ p i,crossOrder p (crossInverse p i)=i := by decide
    exact h p

def basisTensorQ (kind : Kind) (a b : Fin 4) (w : Fin 4 → Bool) : Q :=
  basisQ kind a (w 0) (w 1)*basisQ kind b (w 2) (w 3)

def cardFormula (kind : Kind) (p : Fin 24) (ctx : Fin 16) (out : Fin 4) : Row := fun a =>
  ∑ u : Bool,∑ v : Bool,dualQ kind out u v *
    ∑ r : Bool,∑ s : Bool,basisQ kind (secondLabel ctx) r s *
      basisTensorQ kind a (permutationData p a)
        (permuteWord (crossPermutation (firstLabel ctx)) ![r,s,u,v])

theorem cardFormula_semantics (kind : Kind) (p : Fin 24) (ctx : Fin 16) (out : Fin 4)
    (c : Fin 4 → Scalar) : evaluate (cardFormula kind p ctx out) c =
      coefficient kind (contract0 (reorder (normalized kind (permutation p) c)
        (crossPermutation (firstLabel ctx))) (E kind (secondLabel ctx))) out := by
  simp only [evaluate,cardFormula,coefficient,Kernel.pair,contract0,reorder,
    normalized,basisTensor,basisTensorQ,E,dual,permutation_apply,map_sum,map_mul,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Fintype.sum_bool]
  simp only [map_add,map_mul,map_zero]
  ring

def planeCount : Kind → ℕ | .standard => 4 | .exotic => 24
def cards (kind : Kind) : Fin 24 → Fin 16 → Fin 4 → Row :=
  match kind with | .standard => standardCards | .exotic => exoticCards
def targets (kind : Kind) : Fin 24 → Fin (planeCount kind) → List Row :=
  match kind with | .standard => standardTargets | .exotic => exoticTargets
def planes (kind : Kind) : Fin (planeCount kind) → Fin 4 → Fin 16 → Q :=
  match kind with | .standard => standardPlanes | .exotic => exoticPlanes
def pivots (kind : Kind) : Fin (planeCount kind) → Fin 4 → Fin 16 :=
  match kind with | .standard => standardPivots | .exotic => exoticPivots
def problem (kind : Kind) (p : Fin 24) : Problem (planeCount kind) := ⟨cards kind p,targets kind p⟩

def delta (p : Fin 24) (col : Fin 16) : Row := fun a =>
  if a=firstLabel col ∧ permutationData p a=secondLabel col then 1 else 0
def coefficientVector (p : Fin 24) (c : Fin 4 → Scalar) (col : Fin 16) : Scalar :=
  if permutationData p (firstLabel col)=secondLabel col then c (firstLabel col) else 0

theorem evaluate_delta (p : Fin 24) (col : Fin 16) (c : Fin 4 → Scalar) :
    evaluate (delta p col) c=coefficientVector p c col := by
  unfold evaluate delta
  rw [Finset.sum_eq_single (firstLabel col)]
  · by_cases h : permutationData p (firstLabel col)=secondLabel col <;> simp [h,coefficientVector]
  · intro i _ hi
    simp [hi]
  · simp

def targetFormula (kind : Kind) (p : Fin 24) (j : Fin (planeCount kind)) (col : Fin 16) : Row :=
  fun a => delta p col a-∑ r : Fin 4,planes kind j r col*delta p (pivots kind j r) a

theorem evaluate_target (kind : Kind) (p : Fin 24) (j : Fin (planeCount kind)) (col : Fin 16)
    (c : Fin 4 → Scalar) : evaluate (targetFormula kind p j col) c=
      coefficientVector p c col-∑ r : Fin 4,embed (planes kind j r col)*coefficientVector p c (pivots kind j r) := by
  simp only [evaluate,targetFormula,map_sub,map_sum,map_mul,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [Finset.sum_comm]
  change evaluate (delta p col) c - _ = _
  rw [evaluate_delta]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [←evaluate_delta p (pivots kind j r) c]
  simp only [evaluate,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Holant.Certificates.EqualityQuaternary.Klein.Finite
