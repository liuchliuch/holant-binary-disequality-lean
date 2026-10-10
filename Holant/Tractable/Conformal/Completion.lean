import Holant.Tractable.Conformal.EOTransport
import Holant.Tractable.Downward

/-! Exact ordered completions under nonzero scaling and simultaneous complement. -/
namespace Holant.Tractable
noncomputable section
namespace Conformal

def mapSignature (opposite : Bool) (c : AlgebraicComplex)
    (g : AnySignature AlgebraicComplex) : AnySignature AlgebraicComplex :=
  ⟨g.1, fun x => c * g.2 (flipWord opposite x)⟩

/-- The transformed layer index, in the original arity. -/
def flipLayer (opposite : Bool) (n d : ℕ) : ℕ := if opposite then n - d else d

theorem flipWord_weight {n : ℕ} (opposite : Bool) (x : Fin n → Bool) :
    Holant.weight (flipWord opposite x) = flipLayer opposite n (Holant.weight x) := by
  cases opposite
  · rfl
  · have h := Holant.weight_compl_add x
    change Holant.weight (complementWord x) = n - Holant.weight x
    exact Nat.eq_sub_of_add_eq h

theorem singleLayer_flip {n d : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Signature.SingleLayer f d) (opposite : Bool) (_hd : d ≤ n)
    (c : AlgebraicComplex) :
    Signature.SingleLayer (fun x => c * f (flipWord opposite x))
      (flipLayer opposite n d) := by
  intro x hx
  have hw : Holant.weight (flipWord opposite x) ≠ d := by
    cases opposite
    · exact hx
    · have hw : Holant.weight (complementWord x) + Holant.weight x = n :=
        Holant.weight_compl_add x
      change Holant.weight x ≠ n - d at hx
      change Holant.weight (complementWord x) ≠ d
      omega
  simp only [hf _ hw, mul_zero]

theorem completeToEO_scale {n d : ℕ} (f : Signature AlgebraicComplex n)
    (c : AlgebraicComplex) :
    Signature.completeToEO (fun x => c * f x) d =
      mapSignature false c (Signature.completeToEO f d) := by
  unfold Signature.completeToEO
  split_ifs <;> apply congrArg (fun f => Sigma.mk _ f) <;> funext x <;>
    simp [Signature.completeWithZeros, Signature.completeWithOnes,
      Signature.tensor_apply, mul_assoc]

private theorem zero_pins_complement {m : ℕ} (x : Fin m → Bool) :
    Signature.unaryPower (Signature.pointMass (K := AlgebraicComplex) false) m
      (complementWord x) =
    Signature.unaryPower (Signature.pointMass (K := AlgebraicComplex) true) m x := by
  apply Finset.prod_congr rfl
  intro j _
  cases hx : x j <;> simp [Signature.pointMass, complementWord, hx]

private theorem one_pins_complement {m : ℕ} (x : Fin m → Bool) :
    Signature.unaryPower (Signature.pointMass (K := AlgebraicComplex) true) m
      (complementWord x) =
    Signature.unaryPower (Signature.pointMass (K := AlgebraicComplex) false) m x := by
  apply Finset.prod_congr rfl
  intro j _
  cases hx : x j <;> simp [Signature.pointMass, complementWord, hx]

/-- Bit complementation switches the appended zero and one pins without moving
any original port or any appended pin. The dependent output arity is proved equal. -/
theorem completeToEO_complement {n d : ℕ} (f : Signature AlgebraicComplex n)
    (hd : d ≤ n) :
    Signature.completeToEO (fun x => f (complementWord x)) (n - d) =
      mapSignature true 1 (Signature.completeToEO f d) := by
  by_cases heq : n = 2 * d
  · have hnd : n - d = d := by omega
    rw [hnd, Signature.completeToEO_eq_self_of_arity_eq_twice _ heq,
      Signature.completeToEO_eq_self_of_arity_eq_twice _ heq]
    simp [mapSignature]
  · by_cases hc : n ≤ 2 * d
    · have hnc : ¬ n ≤ 2 * (n - d) := by omega
      have he : n - 2 * (n - d) = 2 * d - n := by omega
      simp only [Signature.completeToEO, hc, hnc, ↓reduceIte]
      simp only [Signature.completeWithZeros, Signature.completeWithOnes]
      rw [he]
      apply congrArg (fun f => Sigma.mk _ f)
      funext x
      change f (complementWord (fun i => x (Fin.castAdd (2 * d - n) i))) *
        Signature.unaryPower (Signature.pointMass true) _ (fun j => x (Fin.natAdd n j)) =
        1 * (f (fun i => !(x (Fin.castAdd (2 * d - n) i))) *
          Signature.unaryPower (Signature.pointMass false) _
            (fun j => !(x (Fin.natAdd n j))))
      rw [one_mul, ← zero_pins_complement]
      rfl
    · have hnc : n ≤ 2 * (n - d) := by omega
      have he : 2 * (n - d) - n = n - 2 * d := by omega
      simp only [Signature.completeToEO, hc, hnc, ↓reduceIte]
      simp only [Signature.completeWithZeros, Signature.completeWithOnes]
      rw [he]
      apply congrArg (fun f => Sigma.mk _ f)
      funext x
      change f (complementWord (fun i => x (Fin.castAdd (n - 2 * d) i))) *
        Signature.unaryPower (Signature.pointMass false) _ (fun j => x (Fin.natAdd n j)) =
        1 * (f (fun i => !(x (Fin.castAdd (n - 2 * d) i))) *
          Signature.unaryPower (Signature.pointMass true) _
            (fun j => !(x (Fin.natAdd n j))))
      rw [one_mul, ← one_pins_complement]
      rfl

theorem completeToEO_scale_flip {n d : ℕ} (f : Signature AlgebraicComplex n)
    (hd : d ≤ n) (opposite : Bool) (c : AlgebraicComplex) :
    Signature.completeToEO (fun x => c * f (flipWord opposite x))
      (flipLayer opposite n d) =
      mapSignature opposite c (Signature.completeToEO f d) := by
  cases opposite
  · exact completeToEO_scale f c
  · change Signature.completeToEO (fun x => c * f (complementWord x)) (n - d) = _
    rw [completeToEO_scale, completeToEO_complement f hd]
    simp [mapSignature]

end Conformal
end
end Holant.Tractable
