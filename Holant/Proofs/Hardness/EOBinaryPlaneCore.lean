import Holant.Proofs.Hardness.FiveSupportEOOrdering
import Holant.Tractable.Criteria

/-! The literal binary compression of an EO opposite-pair plane. All values
are retained in their original coefficient field. The lift is a formula,
not an assertion that a compressed binary vertex is freely available. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
set_option backward.isDefEq.respectTransparency false

/-- Canonical opposite incidences are (0,1) and (2,3). -/
def pairing : OrientedPerfectPairing 4 where
  count := 2
  ports := {
    toFun := fun p => if p.1=0 then (if p.2 then 1 else 0) else (if p.2 then 3 else 2)
    invFun := ![(0,false),(0,true),(1,false),(1,true)]
    left_inv := by decide
    right_inv := by decide }

def word (z : Fin 2 → Bool) : Fin 4 → Bool := ![z 0,!(z 0),z 1,!(z 1)]

theorem pairing_word (z : Fin 2 → Bool) : pairing.word z=word z := by
  funext i
  fin_cases i <;> rfl

def compress {K : Type*} (M : Signature K 4) : Signature K 2 := fun z=>M (word z)

def lift {K : Type*} [Zero K] (f : Signature K 2) : Signature K 4 :=
  fun x=>if x 1=!(x 0) ∧ x 3=!(x 2) then f ![x 0,x 2] else 0

theorem restrict_eq (M : Signature AlgebraicComplex 4) : pairing.restrict M=compress M := by
  funext z
  exact congrArg M (pairing_word z)

@[simp] theorem compress_lift {K : Type*} [Zero K] (f : Signature K 2) : compress (lift f)=f := by
  funext z
  have hz : (![z 0,z 1] : Fin 2→Bool)=z := by funext i; fin_cases i <;> rfl
  simp [compress,word,lift,hz]

theorem lift_eo {K : Type*} [Field K] (f : Signature K 2) : DenseEOUnitLocal.EOSupport (lift f) := by
  intro x hx
  by_cases hh : x 1=!(x 0) ∧ x 3=!(x 2)
  · have hw : weight x=2 := by
      unfold weight
      simp only [Fin.sum_univ_four,hh.1,hh.2]
      cases x 0 <;> cases x 2 <;> rfl
    exact False.elim (hx hw)
  · simp [lift,hh]

theorem lift_compress {K : Type*} [Field K] (M : Signature K 4)
    (he : DenseEOUnitLocal.EOSupport M) (hb : (entries M).b=0) (hy : (entries M).y=0) :
    lift (compress M)=M := by
  funext x
  have hx : x=![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp only [lift,compress,word,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,Bool.true_eq_false,false_and,ite_false]
  all_goals first
    | rfl
    | exact hb.symm
    | exact hy.symm
    | exact (he _ (by decide)).symm

/-- The compressed matrix is exactly [[c,d],[w,z]], in original values. -/
theorem compress_entries {K : Type*} (M : Signature K 4) :
    compress M ![false,false]=(entries M).c ∧
    compress M ![false,true]=(entries M).d ∧
    compress M ![true,false]=(entries M).w ∧
    compress M ![true,true]=(entries M).z := ⟨rfl,rfl,rfl,rfl⟩

def normalized {K : Type*} (M : Signature K 4) (i : Fin 6) : Signature K 4 :=
  Tensor.reindex (FiveSupportEOOrdering.orderAt i) M

theorem normalized_eo {K : Type*} [Field K] (M : Signature K 4)
    (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6) :
    DenseEOUnitLocal.EOSupport (normalized M i) := by
  intro x hx
  apply he
  have hw : weight (fun j=>x (FiveSupportEOOrdering.orderAt i j))=weight x :=
    Equiv.sum_comp (FiveSupportEOOrdering.orderAt i) (fun j=>if x j then 1 else 0)
  simpa only [hw] using hx

theorem normalized_corners {K : Type*} [Field K] (M : Signature K 4) (i : Fin 6)
    (h0 : FiveSupportEOOrdering.middleCoeff M i=0)
    (h1 : FiveSupportEOOrdering.middleCoeff M (5-i)=0) :
    (entries (normalized M i)).b=0 ∧ (entries (normalized M i)).y=0 := by
  constructor
  · change FiveSupportEOOrdering.middleCoeff (normalized M i) 0=0
    rw [normalized,FiveSupportEOOrdering.reindex_middleCoeff,
      FiveSupportEOOrdering.middleIndexAt_zero]
    exact h0
  · change FiveSupportEOOrdering.middleCoeff (normalized M i) 5=0
    rw [normalized,FiveSupportEOOrdering.reindex_middleCoeff]
    have hi : FiveSupportEOOrdering.middleIndexAt i 5=5-i := by fin_cases i <;> rfl
    simpa only [hi] using h1

theorem normalized_lift {K : Type*} [Field K] (M : Signature K 4)
    (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6)
    (h0 : FiveSupportEOOrdering.middleCoeff M i=0)
    (h1 : FiveSupportEOOrdering.middleCoeff M (5-i)=0) :
    lift (compress (normalized M i))=normalized M i :=
  lift_compress _ (normalized_eo M he i) (normalized_corners M i h0 h1).1
    (normalized_corners M i h0 h1).2

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore
