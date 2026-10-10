import Holant.Platonic.RankDeficientLocalization.Normalization.PhysicalAssembly

/-! Arbitrary-cut flattening ranks under literal local matrices and physical
port permutations. This is independent of the finite deficient certificates. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Platonic.RainbowLocalization
open Holant.Platonic.RainbowLocalization.MatchingCut (Side joinAssignment joinAssignment_true joinAssignment_false)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical

namespace Cut
variable {P : Type*} [Fintype P] [DecidableEq P]

def sideUnion (s : P → Bool) : (Side s true ⊕ Side s false) ≃ P where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun p := if h : s p=true then .inl ⟨p,h⟩ else .inr ⟨p,by cases hs : s p <;> simp_all⟩
  left_inv z := by cases z with
    | inl z => simp [z.property]
    | inr z => simp [z.property]
  right_inv p := by cases hs : s p <;> simp [hs]

theorem product_split (s : P → Bool) (f : P → ℂ) :
    (∏p,f p)=(∏p : Side s true,f p.val)*(∏p : Side s false,f p.val) := by
  have hh := (sideUnion s).prod_comp f
  simpa only [Fintype.prod_sum_type,sideUnion,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr] using hh.symm

def assignments (s : P → Bool) : (P → Bool) ≃ ((Side s true → Bool) × (Side s false → Bool)) where
  toFun x := (fun p => x p.val,fun p => x p.val)
  invFun z := joinAssignment s z.1 z.2
  left_inv x := by
    funext p
    cases hs : s p <;> simp [joinAssignment,hs]
  right_inv z := by
    apply Prod.ext <;> funext p
    · exact joinAssignment_true s z.1 z.2 p
    · exact joinAssignment_false s z.1 z.2 p

variable {n : ℕ}

theorem flatten_action (s : Fin n → Bool) (L : Fin n → Matrix Bool Bool ℂ)
    (h : Signature ℂ n) :
    MatchingCut.flatten s (Signature.coordinateAction L h)=
      binaryProductMatrix (fun p : Side s true => L p.val)*MatchingCut.flatten s h*
        (binaryProductMatrix (fun p : Side s false => L p.val)).transpose := by
  ext x y
  change (∑z : Fin n → Bool,(∏j,L j (joinAssignment s x y j) (z j))*h z)=_
  rw [←(assignments s).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hp (a : Side s true → Bool) (b : Side s false → Bool) :
      (∏j,L j (joinAssignment s x y j) (joinAssignment s a b j))=
        binaryProductMatrix (fun p : Side s true => L p.val) x a*
        binaryProductMatrix (fun p : Side s false => L p.val) y b := by
    rw [product_split s]
    simp only [joinAssignment_true,joinAssignment_false,binaryProductMatrix]
  change (∑a,∑b,(∏j,L j (joinAssignment s x y j) (joinAssignment s a b j))*h (joinAssignment s a b))=_
  simp_rw [hp]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,MatchingCut.flatten,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem flatten_action_rank (s : Fin n → Bool) (L : Fin n → Matrix Bool Bool ℂ)
    (hL : ∀j,(L j).det≠0) (h : Signature ℂ n) :
    (MatchingCut.flatten s (Signature.coordinateAction L h)).rank=(MatchingCut.flatten s h).rank := by
  have hl := binaryProductMatrix_det_isUnit (fun p : Side s true => L p.val) (fun p => hL p.val)
  have hr := binaryProductMatrix_det_isUnit (fun p : Side s false => L p.val) (fun p => hL p.val)
  have hld : (binaryProductMatrix (fun p : Side s true => L p.val)).det≠0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hl)
  have hrd : ((binaryProductMatrix (fun p : Side s false => L p.val)).transpose).det≠0 := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hr)
  rw [flatten_action,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hrd,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hld]

def sideWords (e : Equiv.Perm P) (s : P → Bool) (b : Bool) :
    (Side s b → Bool) ≃ (Side (s ∘ e) b → Bool) where
  toFun x p := x ⟨e p.val,p.property⟩
  invFun x p := x ⟨e.symm p.val,by simpa using p.property⟩
  left_inv x := by funext p; simp
  right_inv x := by funext p; simp

theorem flatten_reindex (e : Equiv.Perm P) (s : P → Bool) (h : Tensor ℂ P) :
    MatchingCut.flatten s (Tensor.reindex e h)=
      (MatchingCut.flatten (s ∘ e) h).submatrix (sideWords e s true) (sideWords e s false) := by
  ext x y
  apply congrArg h
  funext p
  cases hs : s (e p) <;>
    simp [MatchingCut.flatten,Tensor.reindex,joinAssignment,hs,Function.comp_def,sideWords]

theorem flatten_reindex_rank (e : Equiv.Perm P) (s : P → Bool) (h : Tensor ℂ P) :
    (MatchingCut.flatten s (Tensor.reindex e h)).rank=(MatchingCut.flatten (s ∘ e) h).rank := by
  rw [flatten_reindex,Matrix.rank_submatrix]

def pairCut (i j : Fin n) : Fin n → Bool := fun k => decide (k=i ∨ k=j)
def AllPairRanks (h : Signature ℂ n) : Prop :=
  ∀i j : Fin n,i≠j → 2≤(MatchingCut.flatten (pairCut i j) h).rank

theorem allPair_action (L : Fin n → Matrix Bool Bool ℂ) (hL : ∀j,(L j).det≠0)
    (h : Signature ℂ n) : AllPairRanks (Signature.coordinateAction L h) ↔ AllPairRanks h := by
  simp only [AllPairRanks,flatten_action_rank _ L hL h]

theorem allPair_reindex (e : Equiv.Perm (Fin n)) (h : Signature ℂ n) :
    AllPairRanks (Tensor.reindex e h) ↔ AllPairRanks h := by
  have hcut (i j : Fin n) : pairCut (e i) (e j) ∘ e=pairCut i j := by
    funext k
    simp [pairCut,Function.comp_def]
  constructor
  · intro hh i j hij
    have hc := hh (e i) (e j) (fun he => hij (e.injective he))
    rw [flatten_reindex_rank,hcut] at hc
    exact hc
  · intro hh i j hij
    have hc := hh (e.symm i) (e.symm j) (fun he => hij (e.symm.injective he))
    rw [flatten_reindex_rank]
    have hs : pairCut i j ∘ e=pairCut (e.symm i) (e.symm j) := by
      simpa using hcut (e.symm i) (e.symm j)
    rw [hs]
    exact hc

theorem allPair_sixDressing (D : SixDressing) (hD : ∀j,(D.legs j).det≠0) (h : Signature ℂ 6) :
    AllPairRanks (D.tensor h) ↔ AllPairRanks h := by
  rw [SixDressing.tensor,allPair_reindex,allPair_action D.legs hD]

end Cut
end
end Holant.Platonic.RankDeficientLocalization.Normalization
