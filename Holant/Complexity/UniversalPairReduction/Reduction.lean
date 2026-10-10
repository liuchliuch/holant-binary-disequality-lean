import Holant.Complexity.UniversalPairReduction.ValueJoins
import Holant.Complexity.UniversalPairReduction.FiniteFamily
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.AsymmetricReduction
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.SymmetricCount
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Transfer

/-! Complete represented native-X one-pair reduction. Both alternatives contain
actual finite Boolean oracle machines, polynomial actual running-time bounds,
and a bound of three on every actual oracle-query prefix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction
open Holant.Algebraic FixedGadgetSubstitution SmoothingCompiler
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {n s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s 1 arity)

abbrev RepresentedReduction := PolyTimeOracleReduction (inputEncoding s arity) F.encoding
  (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
  (BinaryFamily.value (ValueJoins.signatures F T) BinaryTable.delta) (T.evaluate F)

/-- No EO, parity, charge, tractability, identity-resource or compiler premise.
The only table hypothesis identifies the one native edge label as X. -/
theorem represented_one_pair_reduction
    (hnative : ∀i a b,F.decode (T.edge i a b)=Signature.disequality a b) :
    ∃r : RepresentedReduction F T,ThreeQuery.AtMostQueries r.machine 3 := by
  let G := ValueJoins.signatures F T
  rcases actual_binary_dichotomy (BinaryFamily.family G) with hs|⟨W,hW,hE,ha⟩
  · let r := sourceTransfer (symmetricReduction F T)
      (BinaryFamily.value G BinaryTable.delta) (ValueJoins.symmetric_exact F T hnative hs)
    exact ⟨r,symmetric_atMostThree F T⟩
  · let L := FiniteFamily.labelling G W hW
    have hL : L.sourceNetwork G (fun _ : Fin 1 => Signature.disequality)=W :=
      FiniteFamily.labelled_network G W hW hE
    have hB : QueryFamily.binary G L (Equiv.refl _) false true ≠
        QueryFamily.binary G L (Equiv.refl _) true false := by
      simpa only [QueryFamily.binary_plus,hL] using ha
    let b := QueryFamily.binary G L (Equiv.refl _) false true
    let c := QueryFamily.binary G L (Equiv.refl _) true false
    let r := sourceTransfer (asymmetricReduction F T L b c)
      (BinaryFamily.value G BinaryTable.delta) (ValueJoins.asymmetric_exact F T hnative L hB)
    exact ⟨r,asymmetric_atMostThree F T L b c⟩

end Holant.Complexity.UniversalPairReduction
