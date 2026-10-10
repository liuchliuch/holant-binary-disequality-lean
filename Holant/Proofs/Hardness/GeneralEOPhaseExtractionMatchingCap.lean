import Holant.Proofs.Hardness.GeneralEOPhaseExtractionMatchingNormalForm

/-! Close a prefix of complete pairs while retaining four actual boundary
ports. Tail permutations commute with those physical native contractions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingCap
open Holant Holant.Complexity FixedGadgetSubstitution
namespace M
export GeneralEOPhaseExtractionMatchingNormalForm (value tailPerm merge_tail)
end M
namespace H
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote)
end H
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels)
end R
namespace D
export GeneralEOPhaseExtractionDistance (loop labels exact native central)
end D
set_option backward.isDefEq.respectTransparency false

def capSignature : (k : ℕ) → Signature ℂ (2*k+4) → Signature ℂ 4
  | 0,f => f
  | k+1,f => capSignature k (H.merge f (Equiv.refl _))

def lastPerm : (k : ℕ) → Equiv.Perm (Fin 4) → Equiv.Perm (Fin (2*k+4))
  | 0,p => p
  | k+1,p => M.tailPerm (lastPerm k p)

def lastPort : (k : ℕ) → Fin 4 → Fin (2*k+4)
  | 0,i => i
  | k+1,i => (lastPort k i).succ.succ

theorem lastPort_val (k : ℕ) (i : Fin 4) : (lastPort k i).val=2*k+i.val := by
  induction k with
  | zero => simp [lastPort]
  | succ k ih => simp only [lastPort,Fin.val_succ,ih]; omega

theorem partial_permute (k : ℕ) (f : Signature ℂ (2*k+4)) (p : Equiv.Perm (Fin 4)) :
    capSignature k (Tensor.reindex (lastPerm k p) f)=Tensor.reindex p (capSignature k f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change capSignature k (H.merge (Tensor.reindex (M.tailPerm (lastPerm k p)) f) (Equiv.refl _))=_
    have hm : H.merge (Tensor.reindex (M.tailPerm (lastPerm k p)) f) (Equiv.refl _)=
        Tensor.reindex (lastPerm k p) (H.merge f (Equiv.refl _)) := by
      rw [M.merge_tail]
      rfl
    rw [hm,ih]
    rfl

theorem value_partial (k : ℕ) (f : Signature ℂ (2*k+4)) :
    M.value (k+2) f=M.value 2 (capSignature k f) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (H.merge f (Equiv.refl _))

def cap : (k : ℕ) → Network ℂ (2*k+4) → Network ℂ 4
  | 0,S => S
  | k+1,S => cap k (D.loop (R.reboundary S (Equiv.refl _)))

theorem cap_denote (k : ℕ) (S : Network ℂ (2*k+4)) :
    (cap k S).denote=capSignature k S.denote := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cap,ih,H.merge_denote]
    rfl

variable {s : ℕ} {a : ℕ→ℕ}

def labels : (k : ℕ) → (S : Network ℂ (2*k+4)) →
    Labelling S.shape s 1 a → Labelling (cap k S).shape s 1 a
  | 0,_,SL => SL
  | k+1,S,SL => labels k _ (D.labels _ (R.reboundaryLabels S SL (Equiv.refl _)))

theorem exact (G : (i : Fin s)→Signature ℂ (a i.val)) (k : ℕ)
    (S : Network ℂ (2*k+4)) (SL : Labelling S.shape s 1 a)
    (hS : LabelledNetwork.Exact G S SL) : LabelledNetwork.Exact G (cap k S) (labels k S SL) := by
  induction k with
  | zero => exact hS
  | succ k ih => exact ih _ _ (D.exact G _ _ hS)

theorem native (k : ℕ) (S : Network ℂ (2*k+4)) (hS : ∀e,S.edge e=Signature.disequality) :
    ∀e,(cap k S).edge e=Signature.disequality := by
  induction k with
  | zero => exact hS
  | succ k ih => exact ih _ (D.native _ hS)

theorem central (k : ℕ) (S : Network ℂ (2*k+4))
    (hS : Signature.CentralSupport S.denote) : Signature.CentralSupport (cap k S).denote := by
  induction k with
  | zero => exact hS
  | succ k ih =>
    exact ih _ (D.central _ (GeneralEOCentralHoleCoordinates.reboundary_central S (Equiv.refl _) hS))

theorem selfdual (k : ℕ) (S : Network ℂ (2*k+4))
    (hS : SelfDualPinObstruction.SelfDual S.denote) :
    SelfDualPinObstruction.SelfDual (cap k S).denote := by
  induction k with
  | zero => exact hS
  | succ k ih =>
    apply ih
    rw [H.merge_denote]
    exact GeneralEOPhaseExtractionClosedTomography.merge_selfdual S.denote hS (Equiv.refl _)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingCap
