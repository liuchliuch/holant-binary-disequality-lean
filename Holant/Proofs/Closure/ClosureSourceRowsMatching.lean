import Holant.Proofs.Closure.ClosureSourceRowsActual

/-! Stable-current-deck matching covers every actual ordered q4 card, not
merely the frozen selected closing matrices. Its scalar is restored exactly.
This is derived from the actual stable deck and is not a supplied SourceDeck
or a classification of the marked complete group. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L : Type*} [Field L]

theorem matching_binary_zero_or_nonsingular (H : Set (Binary (K:=L)))
    (hH : ProjectiveMatrixGroup H) (g : Signature L 2) (hg : MatchingOrZero H g) :
    g = 0 ∨ Matrix.det (binaryMatrix g) ≠ 0 := by
  rcases hg with hz | ⟨M,hM,hc,he⟩
  · exact Or.inl hz
  · right
    cases M with
    | mk edges ports matrix scalar =>
      have hp := Fintype.card_congr ports
      simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hp
      have hn : edges = 1 := by omega
      subst edges
      have hab : ports (0,false) ≠ ports (0,true) := by
        intro h
        have h' := ports.injective h
        exact Bool.false_ne_true (congrArg Prod.snd h')
      have hd : Matrix.det (matrix 0) ≠ 0 := SafeBinary.nonsingular hH (hM 0)
      have hform : binaryMatrix g = scalar • matrix 0 ∨
          binaryMatrix g = scalar • (matrix 0).transpose := by
        rw [he]
        have choice (i : Fin 2) : i = 0 ∨ i = 1 := by
          fin_cases i
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases choice (ports (0,false)) with h0 | h0 <;>
          rcases choice (ports (0,true)) with h1 | h1
        · exact False.elim (hab (h0.trans h1.symm))
        · left
          funext a b
          simp [binaryMatrix,Presentation.tensor,productValue,h0,h1]
        · right
          funext a b
          simp [binaryMatrix,Presentation.tensor,productValue,h0,h1,Matrix.transpose_apply]
        · exact False.elim (hab (h0.trans h1.symm))
      rcases hform with hform | hform
      · rw [hform,Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ hc) hd
      · rw [hform,Matrix.det_smul,Matrix.det_transpose]
        exact mul_ne_zero (pow_ne_zero _ hc) hd

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4)
variable (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
include torsion stableDeck

/-- An arbitrary actual closing representative is covered by the real stable
CURRENT deck, using its recovered original-field nonzero coefficient. -/
theorem actualCard_matching (e : Equiv.Perm (Fin 4)) (B : Binary (K:=OI.K G))
    (hB : ActualNonsingular P.family B) :
    MatchingOrZero (actualTransfers P.family) (originalOrderedCard q e B) := by
  obtain ⟨j,c,hc,he⟩ := actualCard_raw_scalar P.family torsion q e B hB
  rw [he]
  exact ContinuationTransport.matching_smul
    (stableDeck _ (sourceCard_in_rawDeck G P torsion q e j)) c hc

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
include core hcore

/-- Every nonzero actual ordered q4 card is a genuine nonsingular binary
over the original current family. This is a consequence, not a safe-row input. -/
theorem actualCard_actual_or_zero (e : Equiv.Perm (Fin 4)) (B : Binary (K:=OI.K G))
    (hB : ActualNonsingular P.family B) :
    originalOrderedCard q e B = 0 ∨
      ActualNonsingular P.family (binaryMatrix (originalOrderedCard q e B)) := by
  rcases matching_binary_zero_or_nonsingular (actualTransfers P.family)
    (actualTransfers_projectiveMatrixGroup P.family (actualTransfers_nonempty P.family) torsion)
    (originalOrderedCard q e B) (actualCard_matching G P torsion q stableDeck e B hB) with hz | hd
  · exact Or.inl hz
  · right
    refine ⟨?_,hd⟩
    change Gadget.Realizes P.family .disequality
      (Holant.Projective.BoundedTorsion.binarySignature (binaryMatrix (originalOrderedCard q e B)))
    rw [binarySignature_binaryMatrix]
    exact (actualCardDirect G P q core hcore e B hB).realizes

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
