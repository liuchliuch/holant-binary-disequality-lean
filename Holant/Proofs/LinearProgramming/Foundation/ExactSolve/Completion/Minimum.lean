import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.BasicPoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Existence of a coordinate-minimizing rational basic point. Downward boundary
motion is followed by a FINITENESS PROOF for rigid points, not a runtime basis
enumeration algorithm. Inverse matrices below are mathematical expressions
used to prove finiteness; no inverse or optimization oracle is a machine.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.Minimum
open Codec FaceMove BasicPoint Matrix
noncomputable section

theorem tangent_neg (d : Raw) (x v : Fin d.dimension → ℚ) (hv : Tangent d x v) : Tangent d x (-v) := by
  constructor
  · intro i; simpa [Pi.neg_apply,mul_neg,Finset.sum_neg_distrib] using congrArg Neg.neg (hv.1 i)
  · intro j hj; simp [hv.2 j hj]

theorem rigid_below (d : Raw) (j : Fin d.dimension) (x : Fin d.dimension → ℚ) (hx : Codec.Feasible d x) :
    ∃ y, Codec.Feasible d y ∧ y j≤x j ∧ Rigid d y := by
  classical
  have aux : ∀ r, ∀ x : Fin d.dimension → ℚ, Codec.Feasible d x →
      d.dimension-(tightSet x).card=r → ∃ y, Codec.Feasible d y ∧ y j≤x j ∧ Rigid d y := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro x hx hr
      by_cases hg : Rigid d x
      · exact ⟨x,hx,le_rfl,hg⟩
      · have hd : ∃ v, Tangent d x v ∧ v ≠ 0 := by simpa [Rigid,not_forall,not_imp] using hg
        obtain ⟨v,hv,hv0⟩ := hd
        obtain ⟨w,hw,hw0,hwj⟩ := orient d x v hv hv0 j
        obtain ⟨t,k,ht,hk,hy,hh,hn,hsub⟩ := first_boundary d x (-w) hx
          (tangent_neg d x w hw) (neg_ne_zero.mpr hw0)
        have hc := Finset.card_lt_card hsub
        have hb := tight_card_le d (move x (-w) t)
        have hlt : d.dimension-(tightSet (move x (-w) t)).card<r := by omega
        obtain ⟨y,hy',hle,hg'⟩ := ih _ hlt _ hy rfl
        refine ⟨y,hy',hle.trans ?_,hg'⟩
        have hm := mul_nonneg ht.le hwj
        dsimp [move]
        linarith
  exact aux _ x hx rfl

abbrev Code (d : Raw) := (Fin d.dimension → InputBounds.Row d) × (Fin d.dimension → Bool)
def rhs (d : Raw) (c : Code d) (i : Fin d.dimension) : ℤ :=
  match c.1 i with
  | .inl k => d.constant k
  | .inr _ => if c.2 i then 1 else 0
def codePoint (d : Raw) (c : Code d) : Fin d.dimension → ℚ :=
  (DeterminantGap.castMatrix (InputBounds.matrix d c.1))⁻¹ *ᵥ (fun i => (rhs d c i : ℚ))

theorem rigid_code (d : Raw) (x : Fin d.dimension → ℚ) (hx : Codec.Feasible d x) (hr : Rigid d x) :
    ∃ c : Code d, codePoint d c=x := by
  classical
  obtain ⟨select,ha,hd⟩ := exists_basis d x hr
  let bits : Fin d.dimension → Bool := fun i =>
    match select i with
    | .inl _ => false
    | .inr k => decide (x k=1)
  let c : Code d := (select,bits)
  have hb (i : Fin d.dimension) : rhs d c i=rightSide d x (select i) := by
    cases h : select i <;> simp [rhs,c,bits,rightSide,h]
  let A := DeterminantGap.castMatrix (InputBounds.matrix d select)
  have hdet : A.det ≠ 0 := by
    have hi : ((InputBounds.matrix d select).det : ℚ) ≠ 0 := by exact_mod_cast hd
    simpa [A,DeterminantGap.castMatrix,← Int.cast_det] using hi
  have he := basis_system d x hx select ha
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨c,?_⟩
  change A⁻¹ *ᵥ (fun i => (rhs d c i : ℚ))=x
  simp_rw [hb]
  rw [← he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hu,Matrix.one_mulVec]

theorem finite_rigid (d : Raw) : Set.Finite {x : Fin d.dimension → ℚ | Codec.Feasible d x ∧ Rigid d x} := by
  classical
  apply (Set.finite_range (codePoint d)).subset
  rintro x ⟨hx,hr⟩
  exact rigid_code d x hx hr

theorem exists_minimum (d : Raw) (j : Fin d.dimension) (h : ∃ x, Codec.Feasible d x) :
    ∃ x, Codec.Feasible d x ∧ Rigid d x ∧ ∀ y, Codec.Feasible d y → x j≤y j := by
  classical
  let s := (finite_rigid d).toFinset
  have hs : s.Nonempty := by
    obtain ⟨x,hx⟩ := h
    obtain ⟨y,hy,hr⟩ := exists_rigid d x hx
    exact ⟨y,by simpa [s] using And.intro hy hr⟩
  obtain ⟨x,hx,hmin⟩ := s.exists_min_image (fun y => y j) hs
  have hx' : Codec.Feasible d x ∧ Rigid d x := by simpa [s] using hx
  refine ⟨x,hx'.1,hx'.2,?_⟩
  intro y hy
  obtain ⟨z,hz,hzy,hr⟩ := rigid_below d j y hy
  exact (hmin z (by simpa [s] using And.intro hz hr)).trans hzy

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.Minimum
