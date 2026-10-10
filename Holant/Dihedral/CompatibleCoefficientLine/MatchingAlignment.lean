import Holant.Dihedral.CompatibleCoefficientLine.PortAlignment

/-! Literal original matching alignment constructs the complementary products;
no post-closure equation or realization is part of the alignment data. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

def edgeOrder {r : ℕ} (e : Fin (r+1)) : Equiv.Perm (Fin (r+1)) := Equiv.swap (Fin.last r) e

def matchingOrder {r : ℕ} (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (e : Fin (r+1)) :
    Equiv.Perm (Fin (2*r+2)) :=
  (pairPorts r).symm.trans ((Equiv.prodCongr (edgeOrder e) (Equiv.refl Bool)).trans p)

theorem matchingOrder_pair {r : ℕ} (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (e d : Fin (r+1)) (b : Bool) : matchingOrder p e (pairPorts r (d,b)) = p (edgeOrder e d,b) := by
  simp [matchingOrder]

theorem matchingOrder_inverse {r : ℕ} (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (e d : Fin (r+1)) (b : Bool) :
    (matchingOrder p e).symm (p (edgeOrder e d,b)) = pairPorts r (d,b) := by
  rw [← matchingOrder_pair p e d b,Equiv.symm_apply_apply]

theorem reindex_matching_product {r : ℕ} (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Fin (r+1) → Mat) (κ : Scalar) (e : Fin (r+1)) :
    Tensor.reindex (matchingOrder p e).symm (productValue p A κ) =
      κ • product r (fun d => A (edgeOrder e d.castSucc)) (A e) := by
  funext x
  have he : A e = A (edgeOrder e (Fin.last r)) := by simp [edgeOrder]
  change κ * (∏ d, A d (x ((matchingOrder p e).symm (p (d,false))))
    (x ((matchingOrder p e).symm (p (d,true))))) = κ * product r _ (A e) x
  rw [he,product_eq_full r (fun d => A (edgeOrder e d)) x]
  apply congrArg (κ * ·)
  symm
  apply Fintype.prod_equiv (edgeOrder e)
  intro d
  rw [matchingOrder_inverse,matchingOrder_inverse]

/-- Equality of the original perfect matching as a literal edge bijection and
endpoint orientation. The parity compatibility is a separate hypothesis. -/
structure MatchingAlignment {r : ℕ}
    (p₀ p₁ : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) where
  edge : Equiv.Perm (Fin (r+1))
  flip : Fin (r+1) → Bool
  endpoints : ∀ e b, p₁ (edge e,b ^^ flip e) = p₀ (e,b)

def MatchingAlignment.factors {r : ℕ} {p₀ p₁ : (Fin (r+1) × Bool) ≃ Fin (2*r+2)}
    (L : MatchingAlignment p₀ p₁) (A : Fin (r+1) → Mat) : Fin (r+1) → Mat :=
  fun e => if L.flip e then Kernel.transpose (A (L.edge e)) else A (L.edge e)

theorem MatchingAlignment.product_eq {r : ℕ} {p₀ p₁ : (Fin (r+1) × Bool) ≃ Fin (2*r+2)}
    (L : MatchingAlignment p₀ p₁) (A : Fin (r+1) → Mat) (κ : Scalar) :
    productValue p₀ (L.factors A) κ = productValue p₁ A κ := by
  funext x
  apply congrArg (κ * ·)
  apply Fintype.prod_equiv L.edge
  intro e
  rw [← L.endpoints e false,← L.endpoints e true]
  cases h : L.flip e <;> simp [MatchingAlignment.factors,h,Kernel.transpose]

/-- The common ordered protected edge forces its index and orientation in the
alignment; these are derived from original endpoint equality. -/
theorem MatchingAlignment.protected_edge {r : ℕ}
    {p₀ p₁ : (Fin (r+1) × Bool) ≃ Fin (2*r+2)} (L : MatchingAlignment p₀ p₁)
    (e₀ e₁ : Fin (r+1)) (h₀ : p₀ (e₀,false)=0) (h₁ : p₁ (e₁,false)=0) :
    L.edge e₀=e₁ ∧ L.flip e₀=false := by
  have h := L.endpoints e₀ false
  rw [h₀,← h₁] at h
  have hh := p₁.injective h
  exact ⟨congrArg Prod.fst hh,by simpa using congrArg Prod.snd hh⟩

end Holant.Dihedral.CompatibleCoefficientLine
