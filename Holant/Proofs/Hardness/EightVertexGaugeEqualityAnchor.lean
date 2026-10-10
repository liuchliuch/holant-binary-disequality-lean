import Holant.Proofs.Hardness.EightVertexGaugeDenseOutcome
import Holant.Proofs.Closure.ClosureMarkedDihedral
import Holant.EightVertex.ProductAnchor.Source

/-! An actual equality anchor from the positive dense gauge branch. The
primitive root forces the complete rotation order to be four. Four supplied
reflection representatives then equalize the original port weights, retaining
every representative multiplier and every native-X attachment. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeEqualityAnchor
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open StableDenseResidualGaugeCore
open Holant.Projective.CyclicDressing
open EightVertexGaugePhysicalOutcome EightVertexGaugeFamily EightVertexGaugeParity
open scoped BigOperators

theorem order_eq_four {m : ℕ} (hm : 3 ≤ m) (omega : ℂˣ)
    (primitive : IsPrimitiveRoot omega m)
    (phases : ∀ t : AlgebraicComplex, Roots m t → t ^ 4 = 1) : m = 4 := by
  have positive : 0 < m := by omega
  have hp := phases
    (Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedral.liftRoot positive omega primitive)
    (Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedral.liftRoot_root positive omega primitive)
  have hc : (omega : ℂ) ^ 4 = 1 := by
    simpa only [map_pow,map_one,
      Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedral.liftRoot_coe] using
      congrArg Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedral.inclusion hp
  have hu : omega ^ 4 = 1 := Units.ext hc
  have hd := primitive.dvd_of_pow_eq_one 4 hu
  have upper : m ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hne : m ≠ 3 := by
    rintro rfl
    norm_num at hd
  omega

theorem reflection_action (mu t : AlgebraicComplex) (ht : t ≠ 0) :
    Kernel.mul (scale mu (S t)) Signature.disequality =
      (mu * t) • Holant.Projective.CyclicPhasePencil.phase t⁻¹ := by
  funext x y
  cases x <;> cases y <;>
    simp [scale,S,R,diagonalKernel,Kernel.mul_apply,Signature.disequality,
      Holant.Projective.CyclicPhasePencil.phase,
      Holant.Projective.CyclicPhasePencil.diagonal,ht]

/-- Exact scalar accounting for the four physical reflections. -/
theorem dressing_value (a : AlgebraicComplex) (u mu t : Fin 4 → AlgebraicComplex)
    (ht : ∀ i, t i ≠ 0) :
    physicalDressing (weighted a u) (fun i => scale (mu i) (S (t i))) =
      weighted (a * ∏ i, mu i * t i) (fun i => u i / t i) := by
  have hlocal : (fun i => Kernel.mul (scale (mu i) (S (t i))) Signature.disequality) =
      (fun i => (mu i * t i) • Holant.Projective.CyclicPhasePencil.phase (t i)⁻¹) :=
    funext (fun i => reflection_action (mu i) (t i) (ht i))
  funext x
  unfold physicalDressing
  rw [hlocal,phase_action,weighted_value,weighted_value]
  have hp : (∏ i, if x i then u i / t i else 1) =
      (∏ i, ((t i)⁻¹) ^ (if x i then 1 else 0 : ℕ)) *
        (∏ i, if x i then u i else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> simp [div_eq_mul_inv,mul_comm]
  rw [hp]
  split <;> ring

theorem constant_weights_dense (a r : AlgebraicComplex) (ha : a ≠ 0) (hr : r ≠ 0) :
    Holant.EightVertex.ProductAnchor.DenseForm (weighted a (fun _ => r)) := by
  refine ⟨a,r,ha,hr,(fun _ => false),?_⟩
  intro x
  rw [weighted_value]
  have hp : (∏ i : Fin 4, if x i then r else 1) = r ^ weight x := by
    calc
      _ = ∏ i : Fin 4, r ^ (if x i then 1 else 0 : ℕ) := by
        apply Finset.prod_congr rfl
        intro i _
        cases x i <;> simp
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  simp [hp,Holant.EightVertex.ProductAnchor.bitSign]

/-- Every correcting phase is represented by an actual old-family binary;
the normalized row is never admitted as an independent resource. -/
theorem anchor_of_fourths (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F 4) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (fourths : ∀ i, u i ^ 4 = u 0 ^ 4)
    (actual : Gadget.Realizes F .disequality (weighted a u)) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor F := by
  let t : Fin 4 → Phase 4 := fun i => ⟨u i / u 0,by
    change (u i / u 0) ^ 4 = 1
    rw [div_pow,fourths i,div_self (pow_ne_zero 4 (hu 0))]⟩
  let c := a * ∏ i, reps.multiplier true (t i) * (t i).val
  have ht : ∀ i, (t i).val ≠ 0 := fun i => div_ne_zero (hu i) (hu 0)
  have hc : c ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun i _ =>
    mul_ne_zero (reps.multiplier_ne_zero true (t i)) (ht i)))
  have hn : (fun i => u i / (t i).val) = (fun _ => u 0) := by
    funext i
    dsimp [t]
    field_simp [hu i]
  have hm : (fun i => reps.matrix true (t i)) =
      (fun i => scale (reps.multiplier true (t i)) (S (t i).val)) := by
    funext i
    simpa [standard] using reps.normal_form true (t i)
  have hd := realizes_physicalDressing F (weighted a u)
    (fun i => reps.matrix true (t i)) actual (fun i => reps.actual true (t i))
  rw [hm,dressing_value a u _ _ ht,hn] at hd
  exact Holant.EightVertex.ProductAnchor.dense_realizing_family_anchor _
    (constant_weights_dense c (u 0) hc (hu 0)) F hd

theorem weighted_anchor_or_bad {m : ℕ} (hm : 3 ≤ m) (omega : ℂˣ)
    (primitive : IsPrimitiveRoot omega m) (F : SignatureFamily AlgebraicComplex)
    (hI : RetainsIdentity F) (reps : MonomialRepresentatives F m)
    (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex)
    (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (actual : Gadget.Realizes F .disequality (weighted a u)) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor F ∨ BadBinary F m := by
  classical
  rcases EightVertexGaugePhaseInsertion.constraints_or_bad hm F hI reps a u ha hu actual with
    ⟨_,phases⟩ | bad
  · have hm4 := order_eq_four hm omega primitive phases
    subst m
    by_cases decks : ∀ i : Fin 3, MonomialPhysicalDeck reps (row a u i)
    · exact Or.inl (anchor_of_fourths F reps a u ha hu
        (physical_decks_fourths hm F reps a u ha hu decks) actual)
    · obtain ⟨i,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps a u actual decks
      exact Or.inr ⟨_,hn,fun hg => ho
        ((EightVertexGaugeRepresentativeLines.line_iff_group (by omega) F reps _).mpr hg),hr,
        physical_card_parity F reps _ (onPorts_even _ _ _ _ _ _ _) e p t⟩
  · exact Or.inr bad

theorem dense_anchor_or_bad {m : ℕ} (hm : 3 ≤ m) (omega : ℂˣ)
    (primitive : IsPrimitiveRoot omega m) (F : SignatureFamily AlgebraicComplex)
    (hI : RetainsIdentity F) (reps : MonomialRepresentatives F m)
    (M : Signature AlgebraicComplex 4) (actual : Gadget.Realizes F .disequality M)
    (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
    (products : StableDenseResidualAlgebra.Products M) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor F ∨ BadBinary F m := by
  obtain ⟨u,hu,hM⟩ := StableDenseResidualGaugeExistence.algebraic_factor M even products
    dense.1 dense.2.1 dense.2.2.1 dense.2.2.2.1 dense.2.2.2.2.1
  apply weighted_anchor_or_bad hm omega primitive F hI reps (entries M).a u dense.1 hu
  simpa only [← hM] using actual

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeEqualityAnchor
end
