import Holant.Proofs.Hardness.GeneralEORootNormSource
import Holant.Proofs.Hardness.GeneralEONegativeClosedSupport

/-! Exact support boundary of genuine ARS. Complementary support makes
either weak support-sign condition equivalent to ternary-XOR closure. This
does not assert unpinned hardness for an ARS support obstruction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSSupport
open Holant Holant.Tractable
namespace F
export SelfDualPinObstruction (flip)
end F
namespace S
export GeneralEOPhaseExtractionSource (inclusion)
end S
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem complement_support (f : Signature AlgebraicComplex n)
    (h : GeneralEOARSBoundary.ARSUpToScale (fun x => S.inclusion (f x))) :
    ∀ x, f (F.flip x) ≠ 0 ↔ f x ≠ 0 := by
  intro x
  have hn := GeneralEOARSBoundary.opposite_norm (fun x => S.inclusion (f x)) h x
  have he : S.inclusion (f (F.flip x)) ≠ 0 ↔ S.inclusion (f x) ≠ 0 := by
    calc
      _ ↔ ‖S.inclusion (f (F.flip x))‖ ≠ 0 := norm_ne_zero_iff.symm
      _ ↔ ‖S.inclusion (f x)‖ ≠ 0 := by rw [hn]
      _ ↔ _ := norm_ne_zero_iff
  simpa using he

theorem flip_triple (x y z : Fin n → Bool) :
    tripleXor (F.flip x) (F.flip y) (F.flip z) = F.flip (tripleXor x y z) := by
  funext i
  simp only [tripleXor,F.flip]
  cases x i <;> cases y i <;> cases z i <;> rfl

theorem supports_iff_closed (f : Signature AlgebraicComplex n)
    (complements : ∀ x, f (F.flip x) ≠ 0 ↔ f x ≠ 0) (sign : EOSign) :
    EONegativeWitness.Supports sign ⟨n,f⟩ ↔ GeneralEONegativeClosedSupport.Closed f := by
  constructor
  · intro support x y z hx hy hz
    by_contra missing
    have positive := (support x y z hx hy hz).resolve_left (fun live => live missing)
    have flippedMissing : f (F.flip (tripleXor x y z)) = 0 := by
      by_contra live
      exact ((complements _).mp live) missing
    have negative := support (F.flip x) (F.flip y) (F.flip z)
      ((complements x).mpr hx) ((complements y).mpr hy) ((complements z).mpr hz)
    dsimp only at negative
    rw [flip_triple,flippedMissing] at negative
    have negcharge : charge (F.flip (tripleXor x y z)) = -charge (tripleXor x y z) :=
      Holant.charge_compl _
    rcases negative with impossible | negative
    · exact impossible rfl
    · rw [negcharge,mul_neg] at negative
      omega
  · intro closed x y z hx hy hz
    exact Or.inl (closed x y z hx hy hz)

theorem ars_supports_iff_closed (f : Signature AlgebraicComplex n)
    (h : GeneralEOARSBoundary.ARSUpToScale (fun x => S.inclusion (f x))) (sign : EOSign) :
    EONegativeWitness.Supports sign ⟨n,f⟩ ↔ GeneralEONegativeClosedSupport.Closed f :=
  supports_iff_closed f (complement_support f h) sign

theorem ars_nonclosed_failures (f : Signature AlgebraicComplex n)
    (h : GeneralEOARSBoundary.ARSUpToScale (fun x => S.inclusion (f x)))
    (notClosed : ¬GeneralEONegativeClosedSupport.Closed f) :
    ¬EONegativeWitness.Supports .positive ⟨n,f⟩ ∧
      ¬EONegativeWitness.Supports .negative ⟨n,f⟩ :=
  ⟨fun hp => notClosed ((ars_supports_iff_closed f h .positive).mp hp),
    fun hn => notClosed ((ars_supports_iff_closed f h .negative).mp hn)⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSSupport
