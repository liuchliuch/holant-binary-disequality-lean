import Holant.Proofs.Closure.ClosureMarkedShiftParameters

/-! A source-grounded obstruction to treating a shifted-A sector deck as a
standard native-M deck. The SAME selected actual original-field reflection
has table proportional to S(-eta), although its sector transfer is X. Derived
Even m and native-Z absence force this table outside groupM m. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
open ClosureMarkedShiftConjugator.Reflection
open ClosureMarkedShiftParameters.Reflection
variable {L : Type*} [Field L] [NumberField L]

/-- The antidiagonal phase can be read exactly from its two nonzero entries. -/
theorem S_mem_groupM_iff (m : ℕ) (t : Scalar) : S t ∈ groupM m ↔ Roots m t := by
  constructor
  · rintro ⟨u,hu,h | h⟩
    · obtain ⟨c,hc,he⟩ := h
      have hh := congrFun (congrFun he true) false
      simp [S,R,Kernel.mul_apply,Signature.disequality,diagonalKernel,scale] at hh
    · obtain ⟨c,hc,he⟩ := h
      have h10 := congrFun (congrFun he true) false
      have h01 := congrFun (congrFun he false) true
      simp [S,R,Kernel.mul_apply,Signature.disequality,diagonalKernel,scale] at h10 h01
      have hc1 : c = 1 := h10.symm
      have htu : t = u := by simpa [hc1] using h01
      simpa [htu] using hu
  · intro ht
    exact ⟨t,ht,Or.inr (ProjectivelyEqual.refl _)⟩

/-- Nonzero coordinate scalars cannot repair the missing standard phase. -/
theorem scale_groupM_iff (m : ℕ) (c : Scalar) (hc : c ≠ 0) (T : Holant.Marked.Mat) :
    scale c T ∈ groupM m ↔ T ∈ groupM m := by
  constructor
  · intro h
    have hh := projectiveFamily_scale m R S h (inv_ne_zero hc)
    have he : scale c⁻¹ (scale c T) = T := by funext a b; simp [scale,hc]
    rwa [he] at hh
  · exact fun h => projectiveFamily_scale m R S h hc

variable {φ : L →+* Scalar} {F : SignatureFamily L} {torsion : ResidualTorsion F}
variable (Q : ClosureMarkedShiftReflection.Reflection φ F torsion)

/-- The source-field pivot and algebraic square-root multiplier remain visible. -/
theorem chosen_table : transport Q.basis (Matrix.map (actualRepresentative F torsion Q.key) φ) =
    scale ((φ Q.multiplier / Q.square) / 2) (S (-Q.eta)) := by
  rw [transport_eq_transfer,Q.chosen_sector]
  have hi : sectorEdgeInverse Q.basis = scale (1/2) (R (-Q.eta)) :=
    edgeInverseA_eta Q.square_nonzero Q.square_eq
  rw [hi,scale_mul]
  have he : Kernel.mul Signature.disequality (R (-Q.eta)) = S (-Q.eta) := rfl
  rw [he]
  congr 1
  simp [div_eq_mul_inv]

theorem chosen_table_multiplier_nonzero : (φ Q.multiplier / Q.square) / 2 ≠ 0 :=
  div_ne_zero Q.chosen_multiplier_nonzero (by norm_num)

variable (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
variable (hX : group φ F torsion ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
variable (h2 : Nat.card (group φ F torsion) ≠ 2) (h4 : Nat.card (group φ F torsion) ≠ 4)
variable (hZ : zClass ∉ group φ F torsion)

include hZ
/-- The actual shifted parameter's m-th power is exactly -1, not just non-root. -/
theorem eta_power_negative : Q.eta ^ (Q.selected hX h2 h4).m = -1 := by
  have hs : (Q.eta ^ (Q.selected hX h2 h4).m)^2 = 1 := by
    rw [←pow_mul,Nat.mul_comm]
    exact Q.eta_root hX h2 h4
  rcases sq_eq_one_iff.mp hs with he | he
  · exact (Q.eta_not_root hX h2 h4 hZ he).elim
  · exact he

include hI
/-- Derived evenness makes the actual table phase -eta an excluded phase too. -/
theorem negative_eta_not_root : ¬ Roots (Q.selected hX h2 h4).m (-Q.eta) := by
  intro h
  have he : Roots (Q.selected hX h2 h4).m Q.eta := by
    unfold Roots at *
    rw [neg_pow,(Q.selected_even hI hX h2 h4).neg_one_pow,one_mul] at h
    exact h
  exact Q.eta_not_root hX h2 h4 hZ he

/-- This is a genuine actual-key obstruction, at the SAME produced basis. -/
theorem chosen_table_not_groupM :
    transport Q.basis (Matrix.map (actualRepresentative F torsion Q.key) φ) ∉
      groupM (Q.selected hX h2 h4).m := by
  rw [chosen_table Q,scale_groupM_iff _ _ (chosen_table_multiplier_nonzero Q),S_mem_groupM_iff]
  exact negative_eta_not_root Q hI hX h2 h4 hZ

omit hI hZ in
/-- Closed on the actual branch guards: no reflection, phase or model is supplied. -/
theorem selected_actual_obstruction (φ : L →+* Scalar) (F : SignatureFamily L)
    (torsion : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hX : group φ F torsion ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (hnc : ¬ IsCyclic (group φ F torsion))
    (h2 : Nat.card (group φ F torsion) ≠ 2) (h4 : Nat.card (group φ F torsion) ≠ 4)
    (hZ : zClass ∉ group φ F torsion) :
    let Q := ClosureMarkedShiftReflection.select φ F torsion hX hnc
    ActualNonsingular F (actualRepresentative F torsion Q.key) ∧
      transport Q.basis (Matrix.map (actualRepresentative F torsion Q.key) φ) ∉
        groupM (Q.selected hX h2 h4).m := by
  dsimp only
  let Q := ClosureMarkedShiftReflection.select φ F torsion hX hnc
  exact ⟨Q.actual,chosen_table_not_groupM Q hI hX h2 h4 hZ⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
