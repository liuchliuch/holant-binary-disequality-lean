import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSquareSupport

/-! Reciprocal elimination for sparse affine-square rows. Seven positive,
unchanged original copies realize the support-preserving reciprocal with one
explicit nonzero original-field scalar. Each original port keeps its incidence
parity, so this construction can be inserted into an even-occurrence network.
The class-closure lemmas justify reciprocal cancellation in regularization. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSquareReciprocal
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle
  (evaluate evaluate_replicate)
end B
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences
  (occurrences occurrences_replicate)
end O
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace S
export OrdinaryNegativeAffineSquareSupport (eighth_equal scale scale_nonzero base base_nonzero)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

section Field
variable {K : Type*} [Field K] {n m : ℕ}
variable (f : Signature K n) (a : Fin n→Bool) (ha : f a≠0)
variable (height : ∀x,f x≠0 → f x^8=f a^8)

include height in
/-- The convention inverse(0)=0 preserves the exact sparse support. -/
theorem seven_value (x : Fin n→Bool) : f x^7=f a^8*(f x)⁻¹ := by
  by_cases hx : f x=0
  · simp [hx]
  · apply (mul_right_cancel₀ hx)
    rw [mul_assoc,inv_mul_cancel₀ hx,mul_one]
    calc
      f x^7*f x=f x^8 := by ring
      _=f a^8 := height x hx

include height in
theorem seven_restriction (p : Fin n→Bool ⊕ Fin m) (z : Fin m→Bool) :
    B.evaluate f (List.replicate 7 p) z=f a^8*(f (T.substitute p z))⁻¹ := by
  rw [B.evaluate_replicate]
  exact seven_value f a height _

/-- A reciprocal block has exactly the same free-incidence parity as the
single original minor it replaces, for arbitrary identifications and pins. -/
theorem seven_incidence (p : Fin n→Bool ⊕ Fin m) (j : Fin m) :
    O.occurrences (List.replicate 7 p) j % 2=O.occurrences [p] j % 2 := by
  rw [O.occurrences_replicate]
  have h := O.occurrences_replicate p 1 j
  simp only [List.replicate_one,one_mul] at h
  rw [h,Nat.mul_mod]
  norm_num

end Field

section Original
variable {n m : ℕ} (K : IntermediateField ℚ AlgebraicComplex) (f : Signature K n)
variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2)) (nonzero : f≠0)

def base : Fin n→Bool := Classical.choose (show ∃x,f x≠0 from by
  by_contra! h
  exact nonzero (funext h))

theorem base_nonzero : f (base K f nonzero)≠0 := Classical.choose_spec (show ∃x,f x≠0 from by
  by_contra! h
  exact nonzero (funext h))

def coefficient : K := f (base K f nonzero)^8

theorem coefficient_nonzero : coefficient K f nonzero≠0 := pow_ne_zero 8 (base_nonzero K f nonzero)

include square in
theorem eighth_equal (x y : Fin n→Bool) (hx : f x≠0) (hy : f y≠0) : f x^8=f y^8 := by
  apply Subtype.ext
  exact S.eighth_equal (fun x=>(f x : AlgebraicComplex)) square x y
    (fun h=>hx (Subtype.ext h)) (fun h=>hy (Subtype.ext h))

include square in
/-- All seven copies and their common scalar lie in the unchanged original
coefficient field. No inverse-valued vertex is adjoined. -/
theorem original_reciprocal (p : Fin n→Bool ⊕ Fin m) (z : Fin m→Bool) :
    B.evaluate f (List.replicate 7 p) z=
      coefficient K f nonzero*(f (T.substitute p z))⁻¹ :=
  seven_restriction f (base K f nonzero)
    (fun x hx=>eighth_equal K f square x _ hx (base_nonzero K f nonzero)) p z

end Original

/-- Positive powers retain the literal Affine support/phase representation. -/
theorem affine_power {n : ℕ} (f : Signature AlgebraicComplex n) (h : Affine f) (k : ℕ) :
    Affine (fun x=>f x^k) := by
  induction k with
  | zero => simpa using affine_constant n 1
  | succ k ih => simpa only [pow_succ] using ih.mul h

/-- The reciprocal is zero off the original affine support. -/
theorem affine_inverse {n : ℕ} (f : Signature AlgebraicComplex n) (h : Affine f) :
    Affine (fun x=>(f x)⁻¹) := by
  by_cases hz : f=0
  · subst f
    exact Or.inl (by funext x; simp)
  obtain ⟨a,ha⟩ : ∃a,f a≠0 := by
    by_contra! hh
    exact hz (funext hh)
  have power := (affine_power f h 3).scale (f a^4)⁻¹
  convert power using 1
  funext x
  by_cases hx : f x=0
  · simp [hx]
  · have hp := h.fourth_power_eq x a hx ha
    apply (mul_right_cancel₀ hx)
    rw [inv_mul_cancel₀ hx]
    calc
      1=(f a^4)⁻¹*f a^4 := (inv_mul_cancel₀ (pow_ne_zero 4 ha)).symm
      _=(f a^4)⁻¹*f x^4 := by rw [hp]
      _=((f a^4)⁻¹*f x^3)*f x := by ring

/-- The square of a coordinate eighth-root twist is an Affine multiplier. -/
theorem twist_square_affine {n : ℕ} (alpha : Fin n→Bool) :
    Affine (fun x : Fin n→Bool => ∏j,if alpha j && x j then imaginaryUnit else 1) := by
  have h (s : Finset (Fin n)) :
      Affine (fun x : Fin n→Bool=>∏j∈s,if alpha j && x j then imaginaryUnit else 1) := by
    induction s using Finset.induction_on with
    | empty => simpa using affine_constant n 1
    | @insert j s hj ih =>
      have hjphase : Affine (fun x : Fin n→Bool=>if alpha j && x j then imaginaryUnit else 1) := by
        cases ha : alpha j
        · simpa using affine_constant n 1
        · simpa only [Bool.true_and,fourthRootPhase_one] using
            StableHigherCurrentSquareClass.affine_coordinate_phase j 1
      simpa only [Finset.prod_insert hj] using hjphase.mul ih
  exact h Finset.univ

theorem twist_inverse {n : ℕ} (alpha : Fin n→Bool) (f : Signature AlgebraicComplex n) :
    localTwist alpha (fun x=>(f x)⁻¹)=fun x=>
      (∏j,if alpha j && x j then imaginaryUnit else 1)*(localTwist alpha f x)⁻¹ := by
  funext x
  simp only [localTwist_apply]
  let t := ∏j,if alpha j && x j then zetaEight else 1
  have ht : t≠0 := Finset.prod_ne_zero_iff.mpr (by
    intro j _
    split_ifs <;> simp [zetaEight_ne_zero])
  have square : t^2=∏j,if alpha j && x j then imaginaryUnit else 1 := by
    dsimp only [t]
    rw [←Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j _
    split_ifs <;> simp [zetaEight_sq]
  change t*(f x)⁻¹=(∏j,if alpha j && x j then imaginaryUnit else 1)*(t*f x)⁻¹
  rw [←square,mul_inv_rev,pow_two]
  calc
    t*(f x)⁻¹=t*(f x)⁻¹*(t*t⁻¹) := by rw [mul_inv_cancel₀ ht,mul_one]
    _=t*t*((f x)⁻¹*t⁻¹) := by ring

/-- LocalAffine reciprocal closure retains each actual supported marking;
its extra twist is removed by a proved fourth-root coordinate multiplier. -/
theorem localAffine_inverse {n : ℕ} (f : Signature AlgebraicComplex n) (h : LocalAffine f) :
    LocalAffine (fun x=>(f x)⁻¹) := by
  intro alpha supported
  have ha : f alpha≠0 := by
    intro hz
    simp [hz] at supported
  rw [twist_inverse]
  exact (twist_square_affine alpha).mul (affine_inverse _ (h alpha ha))

/-- Uniform eighth-root-twisted Affine is also closed under reciprocal. -/
theorem uniformTwist_inverse {n : ℕ} (f : Signature AlgebraicComplex n)
    (h : Affine (localTwist (fun _=>true) f)) :
    Affine (localTwist (fun _=>true) (fun x=>(f x)⁻¹)) := by
  rw [twist_inverse]
  exact (twist_square_affine _).mul (affine_inverse _ h)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineSquareReciprocal
end
