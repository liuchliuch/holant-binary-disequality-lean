import Holant.Proofs.Hardness.GeneralEOBinarySignRigidity
import Holant.Proofs.Hardness.GeneralEOGeneralPhaseExtraction

/-! The generated binary order-two residual forces a common complement sign
on every actual central graph. Any needed signed binary is extracted from
the source itself, so it is never supplied as a free signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
namespace L
export GeneralEOBinarySignLocal (Square sign_square signedMerge square_of_merges)
end L
namespace T
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote)
end T
namespace S
export GeneralEOPhaseExtractionSigns (Sign)
end S
namespace N
export GeneralEOPhaseExtractionNetwork (Signed network denote value labels exact native central)
end N
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels reboundary_denote)
end R
namespace F
export SelfDualPinObstruction (flip SelfDual)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature ℂ (a i.val))

def BinarySquare : Prop := ∀ (B : Network ℂ 2) (BL : Labelling B.shape s 1 a),
  LabelledNetwork.Exact G B BL → (∀e,B.edge e=Signature.disequality) →
  Signature.CentralSupport B.denote → B.denote ![false,true]^2=B.denote ![true,false]^2

theorem binary_sign (B : Network ℂ 2) (hE : Signature.CentralSupport B.denote)
    (h : B.denote ![false,true]^2=B.denote ![true,false]^2) : S.Sign B.denote := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with hp|hm
  · exact Or.inl (GeneralEOPhaseExtractionSymmetricResidual.binary_selfdual B hE hp)
  · right
    have h00 : B.denote ![false,false]=0 := hE _ (by decide)
    have h11 : B.denote ![true,true]=0 := hE _ (by decide)
    intro x
    have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
    have hf (u v : Bool) : F.flip (![u,v] : Fin 2→Bool)=![!u,!v] := by
      funext i
      fin_cases i <;> rfl
    rw [hx,hf]
    cases x 0 <;> cases x 1 <;> simp [h00,h11,hm]

variable (B : Network ℂ 2) (BL : Labelling B.shape s 1 a) (t : ℂ)
variable (hBL : LabelledNetwork.Exact G B BL) (hBN : ∀e,B.edge e=Signature.disequality)
variable (ht : t≠0) (hBt : N.Signed B t)

include hBL hBN ht hBt in
theorem sign_with_signed (hBinary : BinarySquare G) (n : ℕ) :
    ∀ (U : Network ℂ n) (UL : Labelling U.shape s 1 a),
      LabelledNetwork.Exact G U UL → (∀e,U.edge e=Signature.disequality) →
      Signature.CentralSupport U.denote → S.Sign U.denote := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U UL hL hN hE
    by_cases hn0 : n=0
    · subst n
      left
      intro x
      congr 1
      funext i
      exact Fin.elim0 i
    by_cases hn1 : n=1
    · subst n
      left
      intro x
      rw [hE (F.flip x) (by omega),hE x (by omega)]
    by_cases hn2 : n=2
    · subst n
      exact binary_sign U hE (hBinary U UL hL hN hE)
    obtain ⟨k,rfl⟩ : ∃k,n=k+3 := ⟨n-3,by omega⟩
    have child (e : Equiv.Perm (Fin (k+3))) (b : Bool) :
        S.Sign (N.network B (R.reboundary U e) b).denote := by
      exact ih (k+1) (by omega) _
        (N.labels B _ BL (R.reboundaryLabels U UL e) b)
        (N.exact G B (R.reboundary U e) BL (R.reboundaryLabels U UL e) hBL hL b)
        (N.native B (R.reboundary U e) hBN hN b)
        (N.central B _ t hBt (GeneralEOCentralHoleCoordinates.reboundary_central U e.symm hE) b)
    have plus (e : Equiv.Perm (Fin (k+3))) : S.Sign (T.merge U.denote e) := by
      rw [←T.merge_denote]
      exact child e false
    have square : L.Square U.denote := by
      apply L.square_of_merges U.denote hE
      · intro e
        exact L.sign_square _ (plus e)
      · intro e x
        have hh := L.sign_square _ (child e true) x
        rw [N.denote B _ t hBt,N.denote B _ t hBt] at hh
        simp only [N.value,ite_true,R.reboundary_denote,Tensor.reindex_apply,mul_pow] at hh
        exact mul_left_cancel₀ (pow_ne_zero 2 ht) hh
    exact GeneralEOBinarySignRigidity.sign_of_children U.denote hE square plus

/-- All hypotheses refer to exact original-labelled graphs with native X edges. -/
theorem sign_of_binary_square (hBinary : BinarySquare G) {n : ℕ}
    (U : Network ℂ n) (UL : Labelling U.shape s 1 a)
    (hL : LabelledNetwork.Exact G U UL) (hN : ∀e,U.edge e=Signature.disequality)
    (hE : Signature.CentralSupport U.denote) : S.Sign U.denote := by
  classical
  by_cases hS : F.SelfDual U.denote
  · exact Or.inl hS
  obtain ⟨Q,QL,hQL,hQN,hQE,hQ⟩ := GeneralEOGeneralPhaseExtraction.asymmetric_binary
    G n U UL hL hN hE hS
  have hsq := hBinary Q QL hQL hQN hQE
  have he : Q.denote ![false,true]= -Q.denote ![true,false] :=
    (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_left hQ
  have ht : Q.denote ![false,true]≠0 := by
    intro hz
    have hz' : Q.denote ![true,false]=0 := by simpa [hz] using he.symm
    exact hQ (hz.trans hz'.symm)
  have hQt : N.Signed Q (Q.denote ![false,true]) :=
    ⟨hQE _ (by decide),rfl,by linear_combination he,hQE _ (by decide)⟩
  exact sign_with_signed G Q QL _ hQL hQN ht hQt hBinary n U UL hL hN hE

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignNetwork
