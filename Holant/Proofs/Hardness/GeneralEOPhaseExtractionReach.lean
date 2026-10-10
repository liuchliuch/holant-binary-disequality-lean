import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSigns
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionDistance

/-! A finite physical construction trace, with actual network constructors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach
open Holant
namespace R
export GeneralEOPinnedDescentNetwork (reboundary)
end R
namespace N
export GeneralEOPhaseExtractionNetwork (network Signed)
end N
namespace S
export GeneralEOPhaseExtractionSigns (Sign reboundary contraction)
end S

inductive Reach (B : Network ℂ 2) : {n m : ℕ} → Network ℂ n → Network ℂ m → Prop where
  | refl {n : ℕ} (T : Network ℂ n) : Reach B T T
  | reindex {n m : ℕ} (T : Network ℂ n) (e : Fin n ≃ Fin m) : Reach B T (R.reboundary T e)
  | contract {n : ℕ} (T : Network ℂ (n+2)) (minus : Bool) : Reach B T (N.network B T minus)
  | trans {n m k : ℕ} {T : Network ℂ n} {U : Network ℂ m} {V : Network ℂ k} :
      Reach B T U → Reach B U V → Reach B T V

theorem preserves_sign (B : Network ℂ 2) (t : ℂ) (hB : N.Signed B t)
    {n m : ℕ} {T : Network ℂ n} {U : Network ℂ m} (h : Reach B T U)
    (hT : S.Sign T.denote) : S.Sign U.denote := by
  revert hT
  induction h with
  | refl T => exact id
  | reindex T e => exact S.reboundary T e
  | contract T minus => exact fun hT => S.contraction B T t hB hT minus
  | trans h₁ h₂ ih₁ ih₂ => exact fun hT => ih₂ (ih₁ hT)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach
