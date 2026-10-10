import Holant.Proofs.Dichotomy.Main.PaperControlled.C2NativePairOutcome

/-! Controlled native-X hardness for a non-fourth-root EO pair. The actual
one/two-copy Ising escape is selected internally from the given coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationIsing
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace O
export PaperControlled.C2NativePairOutcome (Macro countingHard powerMacro double_form)
end O
namespace E
export OrdinarySymmetricPairEscape (step escape)
end E
namespace M
export GeneralEOAffinePlaneChain (binary)
end M
namespace S
export GlobalCloseCompletionKleinOrdinaryPair (symmetric)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K]
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable {degree size : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin size)→Signature K (arity i.val))
variable (phi : K→+*ℂ) (N : O.Macro H)

include phi in
theorem hard (a d : K)
    (form : N.network.denote=EOBinaryPlaneCore.lift (M.binary (S.symmetric a d)))
    (ha : a≠0) (hd : d≠0) (fourth : a^4≠d^4) :
    PaperControlledHardness.Hard (RawClosedNetwork.validatedEncoding size 1 arity) F.encoding
      (GeneralEOPinnedDescentAccess.targetValue F H) := by
  have notFourth : (phi (d/a))^4≠1 := by
    intro h
    have ratio : (d/a)^4=1 := phi.injective (by simpa only [map_pow,map_one] using h)
    apply fourth
    exact ((div_eq_one_iff_eq (pow_ne_zero _ ha)).mp (by simpa only [div_pow] using ratio)).symm
  have notOne : (phi (d/a))^2≠1 := by
    intro h
    apply notFourth
    calc
      _=((phi (d/a))^2)^2 := by ring
      _=1 := by rw [h];ring
  have notNegative : (phi (d/a))^2≠ -1 := by
    intro h
    apply notFourth
    calc
      _=((phi (d/a))^2)^2 := by ring
      _=1 := by rw [h];ring
  rcases E.escape (phi (d/a)) notOne notNegative with first|⟨_denom,second⟩
  · exact O.countingHard F H N a d form ha hd
      (GlobalCloseCompletionC2OrdinaryPairOutcome.infinite_of_image phi (d/a) first)
  · have leftNonzero : a^2+d^2≠0 := by
      intro zero
      apply fourth
      linear_combination (a^2-d^2)*zero
    have rightNonzero : 2*a*d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hd
    have ratio : phi ((2*a*d)/(a^2+d^2))=E.step (phi (d/a)) := by
      have nonzeroA : phi a≠0 := (map_ne_zero phi).mpr ha
      have nonzeroSum : phi a^2+phi d^2≠0 := by
        simpa only [map_add,map_pow] using (map_ne_zero phi).mpr leftNonzero
      calc
        phi ((2*a*d)/(a^2+d^2))=(2*phi a*phi d)/(phi a^2+phi d^2) := by
          rw [map_div₀,phi.map_mul,phi.map_mul,phi.map_add,map_pow,map_pow,map_ofNat]
        _=E.step (phi (d/a)) := by
          rw [E.step,map_div₀]
          field_simp [nonzeroA,nonzeroSum]
    apply O.countingHard F H (O.powerMacro H N 1) (a^2+d^2) (2*a*d)
      (O.double_form H N a d form) leftNonzero rightNonzero
    apply GlobalCloseCompletionC2OrdinaryPairOutcome.infinite_of_image phi
    rw [ratio]
    exact second

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationIsing
end
