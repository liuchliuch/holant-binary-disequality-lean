import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2UnsignedIsingSource
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2PairAffine
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairOutcome

/-! An actual ordinary symmetric pair is affine, or its unchanged whole
source is counting hard. The physical-X premise is absent: the unsigned
apex programme supplies the one/two-copy infinite-order branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnsignedPairOutcome
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
namespace O
export GlobalCloseCompletionC2OrdinaryPairOutcome (powerMacro double_form infinite_of_image)
end O
namespace E
export OrdinarySymmetricPairEscape (step escape)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K]
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable {degree s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (arity i.val))
variable (phi : K→+*AlgebraicComplex)

theorem mapped_pair (a d : K) : RingHomRealization.mapSignature phi (P.pair (M.binary (P.symmetric a d)))=
    P.pair (M.binary (P.symmetric (phi a) (phi d))) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [RingHomRealization.mapSignature,P.pair,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3]

theorem inverse_infinite (a d : K) (infinite : ∀n : ℕ,0<n→(d/a)^n≠1) :
    ∀n : ℕ,0<n→(a/d)^n≠1 := by
  intro n hn eqn
  apply infinite n hn
  have h := congrArg (fun t : K=>t⁻¹) eqn
  simpa only [←inv_pow,inv_div,inv_one] using h

variable {β V : Type} (eb : Encoding β Bool) (ev : Encoding V Bool) (value : β→V)
variable (R : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
  eb ev ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) value)

include R in
theorem hard_of_infinite (N : Macro H 4) (a d : K)
    (form : N.network.denote=P.pair (M.binary (P.symmetric a d))) (ha : a≠0) (hd : d≠0)
    (infinite : ∀n : ℕ,0<n→(d/a)^n≠1) : Holant.LocalDrafts.CountingHardness.WitnessCountingHard eb ev value := by
  have binary : M.binary (P.symmetric a d)=BinaryIsingWeights.table a d := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [M.binary,M.bitIndex,P.symmetric,BinaryIsingWeights.table,BinaryIsingWeights.interaction,h0,h1]
  intro α ea count w
  exact ⟨(GlobalCloseCompletionC2UnsignedIsingSource.sourceMacro F a d H N
    (form.trans (congrArg P.pair binary)) ha hd (inverse_infinite a d infinite) w).compose R.reduction⟩

include R in
theorem affine_or_hard (N : Macro H 4) (a d : K)
    (form : N.network.denote=P.pair (M.binary (P.symmetric a d))) :
    Affine (RingHomRealization.mapSignature phi N.network.denote) ∨
      Holant.LocalDrafts.CountingHardness.WitnessCountingHard eb ev value := by
  classical
  by_cases ha : a=0
  · left
    rw [form,mapped_pair,ha,map_zero]
    exact GlobalCloseCompletionC2PairAffine.pair_zero_left _
  by_cases hd : d=0
  · left
    rw [form,mapped_pair,hd,map_zero]
    exact GlobalCloseCompletionC2PairAffine.pair_zero_right _
  by_cases fourth : a^4=d^4
  · left
    rw [form,mapped_pair]
    exact GlobalCloseCompletionC2PairAffine.pair_fourth _ _ ((map_ne_zero phi).mpr ha)
      (by rw [←map_pow,←map_pow,fourth])
  right
  let psi : K→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp phi
  have notFourth : (psi (d/a))^4≠1 := by
    intro eqn
    have ratio : (d/a)^4=1 := psi.injective (by simpa only [map_pow,map_one] using eqn)
    apply fourth
    exact ((div_eq_one_iff_eq (pow_ne_zero _ ha)).mp (by simpa only [div_pow] using ratio)).symm
  have notOne : (psi (d/a))^2≠1 := by
    intro eqn
    apply notFourth
    calc
      _=((psi (d/a))^2)^2 := by ring
      _=1 := by rw [eqn]; ring
  have notNegative : (psi (d/a))^2≠ -1 := by
    intro eqn
    apply notFourth
    calc
      _=((psi (d/a))^2)^2 := by ring
      _=1 := by rw [eqn]; ring
  rcases E.escape (psi (d/a)) notOne notNegative with first|⟨_denom,second⟩
  · exact hard_of_infinite F H eb ev value R N a d form ha hd (O.infinite_of_image psi (d/a) first)
  · have hn : a^2+d^2≠0 := by
      intro zero
      apply fourth
      linear_combination (a^2-d^2)*zero
    have hr : 2*a*d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hd
    have ratio : psi ((2*a*d)/(a^2+d^2))=E.step (psi (d/a)) := by
      have hna : psi a≠0 := (map_ne_zero psi).mpr ha
      have hns : psi a^2+psi d^2≠0 := by simpa only [map_add,map_pow] using (map_ne_zero psi).mpr hn
      simp only [map_div₀,map_mul,map_ofNat,map_add,map_pow,E.step]
      field_simp [hna,hns]
    apply hard_of_infinite F H eb ev value R (O.powerMacro H N 1) (a^2+d^2) (2*a*d)
      (O.double_form H N a d form) hn hr
    apply O.infinite_of_image psi
    rw [ratio]
    exact second

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnsignedPairOutcome
end
