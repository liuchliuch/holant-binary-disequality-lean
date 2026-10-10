import Holant.Proofs.Hardness.GeneralEORootNormNetwork
import Holant.Proofs.Hardness.GeneralEOBinarySignSource

/-! Complete non-ARS source exit. If pin elimination fails, every actual
binary has equal opposite norms. A non-sign binary would force ARS on the
selected original graph by three actual cap tests; the remaining order-two
case enters the existing checked signed source and its original-G programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace S
export GeneralEOPhaseExtractionSource (inclusion CountingHard)
end S
namespace B
export GeneralEOPhaseExtractionFieldBridge (family map_exact map_native map_central)
end B
namespace N
export GeneralEORootNormNetwork (BinaryNorms ars_with_binary)
end N
namespace Sign
export GeneralEOBinarySignSource (BinarySquare binary_norms_map_of_no_elimination pinning_or_hardness)
end Sign
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {s n : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

theorem binary_square_of_nonars_no_elimination
    (noPin : ¬Nonempty (GeneralEOPinEliminationCases.Elimination G))
    (T : Network AlgebraicComplex n) (TL : Labelling T.shape s 1 a)
    (hL : LabelledNetwork.Exact G T TL) (hN : ∀ e,T.edge e = Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    Sign.BinarySquare G := by
  classical
  have norms : N.BinaryNorms (B.family G S.inclusion) :=
    Sign.binary_norms_map_of_no_elimination G noPin
  intro Q QL hQL hQN hQE
  by_contra hsq
  let U := Q.map S.inclusion
  have hUL := B.map_exact G S.inclusion Q QL hQL
  have hUN := B.map_native S.inclusion Q hQN
  have hUE := B.map_central S.inclusion Q hQE
  have hn := norms U QL hUL hUN hUE
  have hne : U.denote ![false,true]^2 ≠ U.denote ![true,false]^2 := by
    intro he
    apply hsq
    apply S.inclusion.injective
    simpa only [U,Network.denote_map,map_pow] using he
  have hp : U.denote ![false,true] ≠ 0 := by
    intro hz
    have hz' : U.denote ![true,false] = 0 := norm_eq_zero.mp (by simpa [hz] using hn.symm)
    exact hne (by rw [hz,hz'])
  have hq : U.denote ![true,false] ≠ 0 := by
    intro hz
    have hz' : U.denote ![false,true] = 0 := norm_eq_zero.mp (by simpa [hz] using hn)
    exact hp hz'
  apply hA
  exact N.ars_with_binary (B.family G S.inclusion) U QL hUL hUN hUE hp hq hne norms n
    (T.map S.inclusion) TL (B.map_exact G S.inclusion T TL hL)
    (B.map_native S.inclusion T hN) (B.map_central S.inclusion T hE)

/-- No successful extraction, group-generation, phase, sign or pinning
hypothesis is supplied. Both alternatives retain the unchanged original G. -/
theorem pinning_or_hardness (T : Network AlgebraicComplex n)
    (TL : Labelling T.shape s 1 a) (hL : LabelledNetwork.Exact G T TL)
    (hN : ∀ e,T.edge e = Signature.disequality) (hE : Signature.CentralSupport T.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.CountingHard G := by
  classical
  by_cases pins : Nonempty (GeneralEOPinEliminationCases.Elimination G)
  · exact Or.inl pins
  exact Sign.pinning_or_hardness G
    (binary_square_of_nonars_no_elimination G pins T TL hL hN hE hA) T TL hL hN hE hA

theorem selected_pinning_or_hardness (i : Fin s)
    (hE : Signature.CentralSupport (G i))
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (B.family G S.inclusion i)) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.CountingHard G := by
  apply pinning_or_hardness G (Network.corolla (G i)) (LabelledNetwork.corolla G i)
    (fun _ => rfl) (fun e => Fin.elim0 e)
  · simpa only [Network.denote_corolla] using hE
  · have he : ((Network.corolla (G i)).map S.inclusion).denote =
        B.family G S.inclusion i := by
      funext x
      rw [Network.denote_map,Network.denote_corolla]
      rfl
    rwa [he]

/-- The complete original-family split retains genuine ARS as its own
terminal alternative; equal complementary norms are never substituted for it. -/
theorem family_outcome (hE : ∀ i, Signature.CentralSupport (G i)) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.CountingHard G ∨
      GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion) := by
  classical
  by_cases hA : GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion)
  · exact Or.inr (Or.inr hA)
  change ¬∀ i, GeneralEOARSBoundary.ARSUpToScale (B.family G S.inclusion i) at hA
  push Not at hA
  obtain ⟨i,hi⟩ := hA
  rcases selected_pinning_or_hardness G i (hE i) hi with pins | hard
  · exact Or.inl pins
  · exact Or.inr (Or.inl hard)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormSource
