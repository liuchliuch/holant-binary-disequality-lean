import Holant.Certificates.EqualityQuaternary.Source

/-! Fixed current representatives and the oriented one-edge matching test.
All changes of representative below retain their exact nonzero scalar. -/
noncomputable section
namespace Holant.Matching.StableQuaternaryBoundary
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
set_option backward.isDefEq.respectTransparency false

def Label : SourceRow → Type
  | .c2 => Bool
  | .monomial m => Bool × Phase m
  | .standardKlein => Fin 4
  | .exoticKlein => Fin 4

def matrix {F : SignatureFamily Scalar} (row : SourceRow) :
    SourceRepresentatives F row → Label row → Mat :=
  match row with
  | .c2 => fun reps k => reps.matrix k
  | .monomial _ => fun reps k => reps.matrix k.1 k.2
  | .standardKlein => fun reps k => reps.matrix k
  | .exoticKlein => fun reps k => reps.matrix k

def orient (reverse : Bool) (B : Mat) : Mat :=
  if reverse then Kernel.transpose B else B

def ActualLine {F : SignatureFamily Scalar} (row : SourceRow)
    (reps : SourceRepresentatives F row) (B : Mat) : Prop :=
  ∃ k c, c≠0 ∧ B=scale c (matrix row reps k)

/-- At two residual ports a perfect matching has exactly one edge. Its
orientation and arbitrary current-group assignment remain explicit. -/
def OrientedMatching {F : SignatureFamily Scalar} (row : SourceRow)
    (reps : SourceRepresentatives F row) (B : Mat) : Prop :=
  ∃ k reverse c, c≠0 ∧ B=scale c (orient reverse (matrix row reps k))

theorem actualLine_scale {F : SignatureFamily Scalar} {row : SourceRow}
    {reps : SourceRepresentatives F row} {B : Mat} (h : ActualLine row reps B)
    (c : Scalar) (hc : c≠0) : ActualLine row reps (scale c B) := by
  obtain ⟨k,d,hd,rfl⟩ := h
  exact ⟨k,c*d,mul_ne_zero hc hd,by funext a b; simp [scale,mul_assoc]⟩

theorem line_of_normalization (B A E : Mat) (c d : Scalar)
    (hc : c≠0) (hd : d≠0) (hB : B=scale c E) (hA : A=scale d E) :
    ∃ s : Scalar,s≠0 ∧ B=scale s A := by
  refine ⟨c/d,div_ne_zero hc hd,?_⟩
  rw [hB,hA]
  funext a b
  simp [scale,div_eq_mul_inv,mul_assoc,hd]

def kleinTransposeSign (kind : Klein.Kind) (k : Fin 4) : ℚ :=
  if k=0 ∨ k=1 ∨ (kind=.standard ∧ k=2) then 1 else -1

theorem klein_transpose (kind : Klein.Kind) (k : Fin 4) :
    Kernel.transpose (Klein.E kind k)=
      scale (kleinTransposeSign kind k) (Klein.E kind (Klein.theta kind k)) := by
  have h : ∀ a b, Klein.basisQ kind k b a=
      (kleinTransposeSign kind k : Klein.Q)*Klein.basisQ kind (Klein.theta kind k) a b := by
    cases kind <;> fin_cases k <;> intro a b <;> cases a <;> cases b <;>
      decide +kernel
  funext a b
  have hh := congrArg Klein.embed (h a b)
  simpa [Kernel.transpose,Klein.E,scale] using hh

theorem kleinTransposeSign_ne_zero (kind : Klein.Kind) (k : Fin 4) :
    (kleinTransposeSign kind k : Scalar)≠0 := by
  unfold kleinTransposeSign
  split_ifs <;> norm_num

theorem klein_transpose_line {F : SignatureFamily Scalar} {kind : Klein.Kind}
    (reps : Klein.Representatives F kind) (k : Fin 4) :
    ∃ j c,c≠0 ∧ Kernel.transpose (reps.matrix k)=scale c (reps.matrix j) := by
  have he : Kernel.transpose (reps.matrix k)=
      scale (reps.multiplier k*(kleinTransposeSign kind k : Scalar))
        (Klein.E kind (Klein.theta kind k)) := by
    rw [reps.normal_form]
    have hs : Kernel.transpose (scale (reps.multiplier k) (Klein.E kind k))=
        scale (reps.multiplier k) (Kernel.transpose (Klein.E kind k)) := rfl
    rw [hs,klein_transpose]
    funext a b
    simp [scale,mul_assoc]
  obtain ⟨c,hc,h⟩ := line_of_normalization _ _ _ _ _
    (mul_ne_zero (reps.multiplier_ne_zero k) (kleinTransposeSign_ne_zero kind k))
    (reps.multiplier_ne_zero (Klein.theta kind k)) he (reps.normal_form _)
  exact ⟨Klein.theta kind k,c,hc,h⟩

theorem monomial_transpose_line {F : SignatureFamily Scalar} {m : ℕ}
    (hm : 0<m) (reps : MonomialRepresentatives F m) (p : Bool) (t : Phase m) :
    ∃ j : Bool × Phase m, ∃ c,c≠0 ∧
      Kernel.transpose (reps.matrix p t)=scale c (reps.matrix j.1 j.2) := by
  cases p with
  | false =>
    refine ⟨(false,t),1,one_ne_zero,?_⟩
    rw [reps.normal_form]
    funext a b
    cases a <;> cases b <;> simp [standard,R,diagonalKernel,Kernel.transpose,scale]
  | true =>
    let t' : Phase m := ⟨t.val⁻¹,t.property.inv⟩
    have ht := t.property.ne_zero hm
    have he : Kernel.transpose (reps.matrix true t)=
        scale (reps.multiplier true t*t.val) (standard true t'.val) := by
      rw [reps.normal_form]
      funext a b
      cases a <;> cases b <;>
        simp [standard,S,R,diagonalKernel,Kernel.mul_apply,Signature.disequality,
          Kernel.transpose,scale,t',ht]
    obtain ⟨c,hc,h⟩ := line_of_normalization _ _ _ _ _
      (mul_ne_zero (reps.multiplier_ne_zero true t) ht)
      (reps.multiplier_ne_zero true t') he (reps.normal_form true t')
    exact ⟨(true,t'),c,hc,h⟩

theorem transpose_actualLine {F : SignatureFamily Scalar} (row : SourceRow)
    (hrow : row.Valid) (reps : SourceRepresentatives F row) (k : Label row) :
    ActualLine row reps (Kernel.transpose (matrix row reps k)) := by
  cases row with
  | c2 =>
    refine ⟨k,1,one_ne_zero,?_⟩
    change Kernel.transpose (reps.matrix k)=scale 1 (reps.matrix k)
    rw [C2.representative_transpose]
    funext a b
    simp [scale]
  | monomial m =>
    exact monomial_transpose_line (by change 3≤m at hrow; omega) reps k.1 k.2
  | standardKlein => exact klein_transpose_line reps k
  | exoticKlein => exact klein_transpose_line reps k

theorem orientedMatching_actualLine {F : SignatureFamily Scalar} (row : SourceRow)
    (hrow : row.Valid) (reps : SourceRepresentatives F row) {B : Mat}
    (h : OrientedMatching row reps B) : ActualLine row reps B := by
  obtain ⟨k,reverse,c,hc,rfl⟩ := h
  cases reverse with
  | false => exact ⟨k,c,hc,rfl⟩
  | true => exact actualLine_scale (transpose_actualLine row hrow reps k) c hc

end Holant.Matching.StableQuaternaryBoundary
