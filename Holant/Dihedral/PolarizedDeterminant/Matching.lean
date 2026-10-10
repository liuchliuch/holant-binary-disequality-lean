import Holant.Dihedral.PolarizedDeterminant.Physical
import Holant.Dihedral.PolarizedDeterminant.Coordinates
import Holant.TensorClosure

/-! Literal tensor factorization on the already fixed oriented global matching.
The result is an exact tensor identity and does not assert that any factor gadget
is available in the signature family. -/
noncomputable section
namespace Holant.Dihedral.PolarizedDeterminant
open scoped BigOperators

/-- The two supported entries are `1` and `rho`, in the recorded edge orientation. -/
def matchingBinary (parity : Bool) (rho : ℂ) : Signature ℂ 2 :=
  fun x => if Bool.xor (x 0) (x 1) = parity then rho ^ (if x 0 then 1 else 0 : ℕ) else 0

/-- The source's fixed support and logical coefficient representation as explicit data.
Every physical port occurs exactly once, in an ordered pair, with its parity label. -/
def matchingTensor {s n : ℕ} (ports : (Σ _ : Fin s, Fin 2) ≃ Fin n)
    (parity : Fin s → Bool) (w : Cube s → ℂ) : Signature ℂ n :=
  fun x => if ∀ i, Bool.xor (x (ports ⟨i, 0⟩)) (x (ports ⟨i, 1⟩)) = parity i
    then w (fun i => x (ports ⟨i, 0⟩)) else 0

/-- The literal ordered decomposition, retaining the exact nonzero global scalar `w(0)`. -/
def matchingDecomposition {s n : ℕ} (ports : (Σ _ : Fin s, Fin 2) ≃ Fin n)
    (parity : Fin s → Bool) (w : Cube s → ℂ) (hzero : w (fun _ => false) ≠ 0) :
    TensorDecomposition ℂ n where
  count := s
  arity := fun _ => 2
  factor := fun i => matchingBinary (parity i) (baseRatio w i)
  ports := ports
  scale := Units.mk0 (w (fun _ => false)) hzero

@[simp] theorem matchingDecomposition_scale {s n : ℕ}
    (ports : (Σ _ : Fin s, Fin 2) ≃ Fin n) (parity : Fin s → Bool)
    (w : Cube s → ℂ) (hzero : w (fun _ => false) ≠ 0) :
    ((matchingDecomposition ports parity w hzero).scale : ℂ) = w (fun _ => false) := rfl

theorem matchingDecomposition_value {s n : ℕ}
    (ports : (Σ _ : Fin s, Fin 2) ≃ Fin n) (parity : Fin s → Bool)
    (w : Cube s → ℂ) (hzero : w (fun _ => false) ≠ 0)
    (hprod : ∀ x, w x = w (fun _ => false) *
      ∏ i, baseRatio w i ^ (if x i then 1 else 0 : ℕ)) :
    (matchingDecomposition ports parity w hzero).value = matchingTensor ports parity w := by
  funext x
  change w (fun _ => false) * (∏ i : Fin s, if Bool.xor (x (ports ⟨i, 0⟩)) (x (ports ⟨i, 1⟩)) = parity i then
    baseRatio w i ^ (if x (ports ⟨i, 0⟩) then 1 else 0 : ℕ) else 0) = _
  rw [Fintype.prod_ite_zero]
  by_cases hs : ∀ i, Bool.xor (x (ports ⟨i, 0⟩)) (x (ports ⟨i, 1⟩)) = parity i
  · simpa [hs, matchingTensor] using (hprod (fun i => x (ports ⟨i, 0⟩))).symm
  · simp [matchingTensor, hs]

/-- **Manuscript Lemma 6.22**, including the exact tensor product consequence.
The support representation is the previously established global matching; the
rank assumptions concern the three flattenings of actual scalar-recorded cards.
No factor realization or reduction direction is postulated by this theorem. -/
theorem source_polarized_determinant_of_representatives {s n m : ℕ} (_hs : 3 ≤ s) (hm : 3 ≤ m)
    (ports : (Σ _ : Fin s, Fin 2) ≃ Fin n) (parity : Fin s → Bool)
    (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (f : Signature ℂ n) (hrep : f = matchingTensor ports parity w)
    (c : Fin s → Fin s → Fin s → ℂˣ) (P : PhysicalGrid m c w)
    (h : PhysicalGridRanks P) :
    (∀ i, baseRatio w i ≠ 0) ∧
    (∀ x, w x = w (fun _ => false) *
      ∏ i, baseRatio w i ^ (if x i then 1 else 0 : ℕ)) ∧
    (matchingDecomposition ports parity w (hw _)).value = f ∧
    Signature.TensorClosure (fun a _ => a = 2) f := by
  obtain ⟨hrho, hprod⟩ := physical_coefficient_product hm c w hw P h
  have hv : (matchingDecomposition ports parity w (hw _)).value = f := by
    rw [matchingDecomposition_value ports parity w (hw _) hprod, ← hrep]
  exact ⟨hrho, hprod, hv, matchingDecomposition ports parity w (hw _), (fun _ => rfl), hv⟩

/-- **Literal source statement of Lemma 6.22.** The rank hypotheses apply directly
to the source-defined two-copy phase sums, with their actual nonzero representative
scalars. There is no supplied card-normalization identity in the hypotheses. -/
theorem source_polarized_determinant {s n m : ℕ} (hs : 3 ≤ s) (hm : 3 ≤ m)
    (ports : (Σ _ : Fin s, Fin 2) ≃ Fin n) (parity : Fin s → Bool)
    (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (f : Signature ℂ n) (hrep : f = matchingTensor ports parity w)
    (c : Fin s → Fin s → Fin s → ℂˣ)
    (scale : Fin s → Fin s → (Fin s → rootsOfUnity m ℂ) → ℂˣ)
    (h : ∀ i k, i ≠ k → ∀ z : Fin s → rootsOfUnity m ℂ,
      ThreeRanks (fun a b xi => (scale i k z : ℂ) *
        (∑ x ∈ sliceWords i k,
          phaseMonomial (fun j => (↑(c i k j * (z j).val) : ℂ)) x *
          w (insert i k a xi x) * w (insert i k b xi x)))) :
    (∀ i, baseRatio w i ≠ 0) ∧
    (∀ x, w x = w (fun _ => false) *
      ∏ i, baseRatio w i ^ (if x i then 1 else 0 : ℕ)) ∧
    (matchingDecomposition ports parity w (hw _)).value = f ∧
    Signature.TensorClosure (fun a _ => a = 2) f :=
  source_polarized_determinant_of_representatives hs hm ports parity w hw f hrep
    c (physicalCards m c w scale) h

end Holant.Dihedral.PolarizedDeterminant
