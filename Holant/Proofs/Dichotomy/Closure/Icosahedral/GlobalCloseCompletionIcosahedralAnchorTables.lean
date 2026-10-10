import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankTwo
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows00
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows01
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows02
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows03
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows04
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows05
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows06
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows07
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows08
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows09
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows10
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows11
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows12
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows13
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows14
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows15
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows16
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows17
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows18
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows19
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows20
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows21
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows22
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows23
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows24
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows25
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows26
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows27
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows28
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows29
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorRows30

/-! Exact assembly of the split kernel-checked I anchor audit, followed by
its original semantic plane and quotient-direction interpretation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
open Holant.Certificates Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralPreservers
open scoped BigOperators

theorem finite_certificate (b c : Fin 31) : finiteCertificate b c := by
  fin_cases b
  · exact anchor_row00 c
  · exact anchor_row01 c
  · exact anchor_row02 c
  · exact anchor_row03 c
  · exact anchor_row04 c
  · exact anchor_row05 c
  · exact anchor_row06 c
  · exact anchor_row07 c
  · exact anchor_row08 c
  · exact anchor_row09 c
  · exact anchor_row10 c
  · exact anchor_row11 c
  · exact anchor_row12 c
  · exact anchor_row13 c
  · exact anchor_row14 c
  · exact anchor_row15 c
  · exact anchor_row16 c
  · exact anchor_row17 c
  · exact anchor_row18 c
  · exact anchor_row19 c
  · exact anchor_row20 c
  · exact anchor_row21 c
  · exact anchor_row22 c
  · exact anchor_row23 c
  · exact anchor_row24 c
  · exact anchor_row25 c
  · exact anchor_row26 c
  · exact anchor_row27 c
  · exact anchor_row28 c
  · exact anchor_row29 c
  · exact anchor_row30 c

noncomputable section

private theorem coefficient_golden (v : GoldenVector) (i : Fin 4) :
    quaternionCoefficient (goldenMatrix v) i=(GoldenInt.eval (v i) : ℂ) :=
  coordinates_golden v i

private theorem coefficient_one (i : Fin 4) :
    quaternionCoefficient (1 : Matrix Bool Bool ℂ) i=if i=0 then 1 else 0 :=
  coordinates_one i

attribute [local simp] coefficient_golden coefficient_one

def anchorTriple (b c : Fin 31) : Fin 3 → TetrahedralPreservers.BinaryMatrix :=
  ![1,representative .icosahedral (baseAnchor .icosahedral b),
    representative .icosahedral (baseAnchor .icosahedral c)]

def anchorPlane (b c : Fin 31) : Submodule ℂ TetrahedralPreservers.BinaryMatrix :=
  Submodule.span ℂ (Set.range (anchorTriple b c))

def normalFunctional (b c : Fin 31) : V →ₗ[ℂ] ℂ where
  toFun v := ∑ i : Fin 4, (GoldenInt.eval (normalRaw b c i) : ℂ)*v i
  map_add' u v := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' a v := by
    simp [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem goldenDot_eval (u v : GoldenVector) :
    (GoldenInt.eval (goldenDot u v) : ℂ) =
      ∑ i : Fin 4, (GoldenInt.eval (u i) : ℂ)*(GoldenInt.eval (v i) : ℂ) := by
  simp [goldenDot,Fin.sum_univ_succ] <;> ring

theorem normal_anchors (b c : Fin 31) (a : Fin 3) :
    normalFunctional b c (coordinates (anchorTriple b c a)) = 0 := by
  fin_cases a
  · simp [normalFunctional,anchorTriple,coordinates_one,normalRaw,Fin.sum_univ_succ]
  · simp [normalFunctional,anchorTriple,representative,raw,anchorRaw,
      coordinates_golden,normalRaw,Fin.sum_univ_succ] <;> ring
  · simp [normalFunctional,anchorTriple,representative,raw,anchorRaw,
      coordinates_golden,normalRaw,Fin.sum_univ_succ] <;> ring

theorem anchorPlane_bound (b c : Fin 31) (hbc : b ≠ c) :
    (deletion .icosahedral (anchorPlane b c)).card ≤ 15 := by
  have hcard := ((finite_certificate b c).resolve_left hbc).1
  have hplane : anchorPlane b c ≤ LinearMap.ker
      ((normalFunctional b c).comp coordinates.toLinearMap) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact normal_anchors b c a
  have hsub : deletion .icosahedral (anchorPlane b c) ⊆ planeIndices b c := by
    intro r hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply (complex_golden_zero_iff _).mp
    rw [goldenDot_eval]
    have hn := hplane ((mem_deletion _ _ _).mp hr)
    change normalFunctional b c (coordinates (representative .icosahedral r)) = 0 at hn
    simpa [normalFunctional,representative,raw] using hn
  exact (Finset.card_le_card hsub).trans hcard

/-- Membership can use the ambient equality decision: all equality
instances are equal, while the finite kernel audit retains its explicit
computational instance in the original definition. -/
private theorem projectionKeys_image (b c : Fin 31) :
    projectionKeys b c=(Finset.univ.filter
      (fun r : Fin 60 => projectionKey (projectedRaw b c r)≠none)).image
        (fun r => (projectionKey (projectedRaw b c r)).getD zeroKey) := by
  unfold projectionKeys
  apply congrArg (fun d : DecidableEq ProjectionKey =>
    @Finset.image (Fin 60) ProjectionKey d
      (fun r => (projectionKey (projectedRaw b c r)).getD zeroKey)
      (Finset.univ.filter fun r : Fin 60 => projectionKey (projectedRaw b c r)≠none))
  exact Subsingleton.elim _ _

theorem mem_projectionKeys (b c : Fin 31) (k : ProjectionKey) :
    k ∈ projectionKeys b c ↔ ∃ r : Fin 60, projectionKey (projectedRaw b c r) = some k := by
  rw [projectionKeys_image]
  constructor
  · rintro h
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp h
    have hn := (Finset.mem_filter.mp hr).2
    cases hk : projectionKey (projectedRaw b c r) with
    | none => exact False.elim (hn hk)
    | some l =>
        simp only [hk,Option.getD_some] at he
        subst l
        exact ⟨r,hk⟩
  · rintro ⟨r,hr⟩
    apply Finset.mem_image.mpr
    exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [hr]⟩,by simp [hr]⟩

theorem projected_eval (b c : Fin 31) (r : Fin 60) (a : Fin 3) :
    (GoldenInt.eval (projectedRaw b c r a) : ℂ) =
      pairing (coordinates (anchorTriple b c a)) (RankTwo.rootPoint false r) := by
  fin_cases a
  · change (GoldenInt.eval (RankTwo.goldenPair (icosahedralRaw 0) (icosahedralRaw r)) : ℂ) =
      pairing (coordinates (1 : TetrahedralPreservers.BinaryMatrix)) (RankTwo.rootPoint false r)
    rw [←RankTwo.standard_identity]
    exact RankTwo.goldenPair_eval _ _
  · change (GoldenInt.eval (RankTwo.goldenPair (anchorRaw b) (icosahedralRaw r)) : ℂ) =
      pairing (coordinates (representative .icosahedral (baseAnchor .icosahedral b)))
        (RankTwo.rootPoint false r)
    exact RankTwo.goldenPair_eval _ _
  · change (GoldenInt.eval (RankTwo.goldenPair (anchorRaw c) (icosahedralRaw r)) : ℂ) =
      pairing (coordinates (representative .icosahedral (baseAnchor .icosahedral c)))
        (RankTwo.rootPoint false r)
    exact RankTwo.goldenPair_eval _ _

/-- The finite lower bound includes actual cross witnesses and original
root indices. None of them is supplied by the caller. -/
theorem anchor_quotient_directions (b c : Fin 31) (hbc : b ≠ c) :
    ∃ m : ℕ, 16 ≤ m ∧ ∃ w : Fin m → Fin 60,
      ∀ a d : Fin m, a ≠ d → ∃ i j : Fin 3,
        pairing (coordinates (anchorTriple b c i)) (RankTwo.rootPoint false (w a)) *
          pairing (coordinates (anchorTriple b c j)) (RankTwo.rootPoint false (w d)) -
        pairing (coordinates (anchorTriple b c i)) (RankTwo.rootPoint false (w d)) *
          pairing (coordinates (anchorTriple b c j)) (RankTwo.rootPoint false (w a)) ≠ 0 := by
  classical
  let D := projectionKeys b c
  let m := D.card
  let e : Fin m ≃ ↑D := (Fintype.equivFinOfCardEq (show Fintype.card ↑D=m from Fintype.card_coe D)).symm
  have hm : 16 ≤ m := ((finite_certificate b c).resolve_left hbc).2
  have hw (a : Fin m) : ∃ r : Fin 60,
      projectionKey (projectedRaw b c r) = some (e a).val :=
    (mem_projectionKeys b c _).mp (e a).property
  choose w hw using hw
  refine ⟨m,hm,w,?_⟩
  intro a d had
  have hkeys : (e a).val ≠ (e d).val := by
    intro he
    exact had (e.injective (Subtype.ext he))
  obtain ⟨i,j,hij⟩ := distinct_keys_cross (hw a) (hw d) hkeys
  refine ⟨i,j,?_⟩
  have hn := GoldenInt.eval_ne_zero _ hij
  have hc : (GoldenInt.eval (projectionCross (projectedRaw b c (w a))
      (projectedRaw b c (w d)) i j) : ℂ) ≠ 0 := by
    intro hz
    exact hn (Complex.ofReal_eq_zero.mp hz)
  rw [projectionCross_eval,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_mul,
    projected_eval,projected_eval,projected_eval,projected_eval] at hc
  simpa only [mul_comm] using hc

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
