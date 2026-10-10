import Holant.Dihedral.SectorRuling.Source

/-! Source E(t),O(t) are literal two-port contractions of the same original
core. Fixed physical representatives and all nonzero normalization scalars are
removed by proved finite-sum identities and scale invariance. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

theorem MatchingSample.scale {m s : ℕ} {q : Signature Scalar (2*s)} (h : MatchingSample m s q)
    (c : Scalar) (hc : c ≠ 0) : MatchingSample m s (c • q) := by
  obtain ⟨p,A,κ,hA,hκ,rfl⟩ := h
  refine ⟨p,A,c*κ,hA,mul_ne_zero hc hκ,?_⟩
  funext x
  simp only [MatchingContractionClosure.productValue,Pi.smul_apply,smul_eq_mul,mul_assoc]

theorem MatchingSample.of_scale {m s : ℕ} {q : Signature Scalar (2*s)} (c : Scalar) (hc : c ≠ 0)
    (h : MatchingSample m s (c • q)) : MatchingSample m s q := by
  have hh := h.scale c⁻¹ (inv_ne_zero hc)
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh

def sectorFirst {s : ℕ} (q : Signature Scalar (2*s+2)) (γ : Bool) : Signature Scalar (2*s) :=
  fun x => q (pair false γ x)
def sectorSecond {s : ℕ} (q : Signature Scalar (2*s+2)) (γ : Bool) : Signature Scalar (2*s) :=
  fun x => q (pair true (!γ) x)

/-- Even: A+tD. Odd: C+tB, in the source original ordered endpoint convention. -/
theorem sector_card_pencil {s : ℕ} (q : Signature Scalar (2*s+2)) (γ : Bool) (t : Scalar) :
    close γ t q=tensorPencil (sectorFirst q γ) (sectorSecond q γ) t := by
  funext x
  cases γ <;> simp [close,M,monomial,tensorPencil,sectorFirst,sectorSecond] <;> ring

/-- In particular source E and O each have the proved ruling, for any original
ordered deleted pair. The actual fixed binary and normalization coefficients
are retained; no free physical basis operation or common support is assumed. -/
theorem source_physical_sector_ruling {m s : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (q : Signature Scalar (2*s+2)) (order : Equiv.Perm (Fin (2*s+2))) (γ : Bool)
    (c : {t : Scalar // Roots m t} → Scalar) (hc : ∀ t,c t ≠ 0)
    (hs : ∀ t : {t : Scalar // Roots m t},
      c t • nativeCardValue (Tensor.reindex order.symm q) ((G.connections (by omega)).binary γ t)=0 ∨
      MatchingSample m s (c t • nativeCardValue (Tensor.reindex order.symm q) ((G.connections (by omega)).binary γ t))) :
    Nonempty (RulingData m s (sectorFirst (Tensor.reindex order.symm q) γ)
      (sectorSecond (Tensor.reindex order.symm q) γ)) := by
  let D := G.connections (by omega : 0<m)
  apply source_sector_ruling hm
  intro t ht
  let z : {t : Scalar // Roots m t} := ⟨t,ht⟩
  have hz : c z*D.multiplier γ z ≠ 0 := mul_ne_zero (hc z) (D.multiplier_ne_zero γ z)
  have he : c z • nativeCardValue (Tensor.reindex order.symm q) (D.binary γ z)=
      (c z*D.multiplier γ z) • tensorPencil
        (sectorFirst (Tensor.reindex order.symm q) γ) (sectorSecond (Tensor.reindex order.symm q) γ) t := by
    rw [D.normalization,actual_close,smul_smul,sector_card_pencil]
  have hh := hs z
  change c z • nativeCardValue (Tensor.reindex order.symm q) (D.binary γ z)=0 ∨
    MatchingSample m s (c z • nativeCardValue (Tensor.reindex order.symm q) (D.binary γ z)) at hh
  rw [he] at hh
  rcases hh with hh|hh
  · left
    by_contra hn
    exact scalar_tensor_nonzero hz hn hh
  · exact Or.inr (MatchingSample.of_scale _ hz hh)

end Holant.Dihedral.SectorRuling
