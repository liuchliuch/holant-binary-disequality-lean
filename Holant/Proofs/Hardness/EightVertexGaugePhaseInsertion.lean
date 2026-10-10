import Holant.Proofs.Hardness.EightVertexGaugeFamily
import Holant.Proofs.Hardness.EightVertexGaugeBinaryBasis
import Holant.Projective.CyclicDressing.Realization

/-! Actual one-port phase insertion. A supplied reflection representative
mu*S(t) is attached by one native X edge, producing scalar a*mu*t and dividing
one original port weight by t. Original and inserted-row physical tests force
t^4=1 for EVERY phase of the same complete monomial group, or supply an actual
bad binary. Combined with the two-I test, all those binary vertices share the
single diagonal affine basis of the gauge family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePhaseInsertion
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open Holant.Projective.CyclicDressing Holant.OpenNetworkComposition
open EightVertexGaugePhysicalOutcome EightVertexGaugeRepresentativeLines EightVertexGaugeFamily
open EightVertexGaugeParity

def weights {K : Type} [Field K] (t : K) (u : Fin 4 → K) : Fin 4 → K :=
  ![u 0/t,u 1,u 2,u 3]

theorem weights_nonzero {K : Type} [Field K] (t : K) (ht : t ≠ 0)
    (u : Fin 4 → K) (hu : ∀ i, u i ≠ 0) : ∀ i, weights t u i ≠ 0 := by
  intro i
  fin_cases i <;> simp [weights,hu,ht]

theorem phase_fourth {K : Type} [Field K] (t : K) (ht : t ≠ 0)
    (u : Fin 4 → K) (hu0 : u 0 ≠ 0)
    (original : ∀ i, u i ^ 4 = u 0 ^ 4)
    (inserted : ∀ i, weights t u i ^ 4 = weights t u 0 ^ 4) : t ^ 4 = 1 := by
  have eq : u 0 ^ 4/t^4 = u 0 ^ 4 := by
    rw [← div_pow]
    calc
      (u 0/t)^4 = weights t u 0 ^ 4 := rfl
      _ = weights t u 1 ^ 4 := (inserted 1).symm
      _ = u 1 ^ 4 := rfl
      _ = u 0 ^ 4 := original 1
  have product := (div_eq_iff (pow_ne_zero 4 ht)).mp eq
  apply mul_left_cancel₀ (pow_ne_zero 4 hu0)
  simpa only [mul_one] using product.symm

/-- Exact native-X splice, keeping the supplied representative multiplier. -/
theorem insertion_value (a mu t : AlgebraicComplex) (ht : t ≠ 0)
    (u : Fin 4 → AlgebraicComplex) :
    onePort (weighted a u) 0 (scale mu (S t)) = weighted (a*mu*t) (weights t u) := by
  rw [onePort_eq_splice]
  funext x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [spliceTensor,kernelSignature,scale,S,R,diagonalKernel,Kernel.mul_apply,
      Signature.disequality,weighted,table,weights] <;>
    field_simp [ht]

theorem insertion_actual {m : ℕ} (hm : 0 < m) (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (actualM : Gadget.Realizes F .disequality (weighted a u))
    (t : Phase m) : Gadget.Realizes F .disequality
      (weighted (a*reps.multiplier true t*t.val) (weights t.val u)) := by
  have h := realizes_onePort F (weighted a u) (reps.matrix true t) actualM (reps.actual true t) 0
  rw [reps.normal_form] at h
  simp only [standard,ite_true] at h
  rwa [insertion_value a (reps.multiplier true t) t.val (t.property.ne_zero hm) u] at h

private theorem bad_of_line {m : ℕ} (hm : 0 < m) (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F m) (B : Mat) (hn : B ≠ 0)
    (ho : ¬ ActualMonomialLine reps B)
    (hr : Gadget.Realizes F .disequality (kernelSignature B))
    (parity : BinaryParity B) : BadBinary F m :=
  ⟨B,hn,fun hg => ho ((line_iff_group hm F reps B).mpr hg),hr,parity⟩

/-- The phase restriction is DERIVED from actual inserted-row tests. The
same original anchor's eighth power is retained for the final binary union. -/
theorem constraints_or_bad {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (actualM : Gadget.Realizes F .disequality (weighted a u)) :
    (u 0 ^ 8 = 1 ∧ ∀ t : AlgebraicComplex, Roots m t → t^4=1) ∨ BadBinary F m := by
  classical
  have positive : 0 < m := by omega
  by_cases original : ∀ k : Fin 3, MonomialPhysicalDeck reps (row a u k)
  · have same := physical_decks_fourths hm F reps a u ha hu original
    let v := EightVertexGaugeFlipPairAlgebra.weights u
    let c := a*u 2*u 3
    have hv : ∀ j, v j ≠ 0 := EightVertexGaugeFlipPairAlgebra.weights_nonzero u hu
    have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero ha (hu 2)) (hu 3)
    have actualFlip : Gadget.Realizes F .disequality (weighted c v) := by
      rw [← EightVertexGaugeFlipPairAlgebra.value a u hu]
      exact EightVertexGaugeFlipPairOutcome.flip_actual F hI _ actualM
    by_cases flipped : ∀ k : Fin 3, MonomialPhysicalDeck reps (row c v k)
    · have sameFlip := physical_decks_fourths hm F reps c v hc hv flipped
      have eighth := EightVertexGaugeFlipPairAlgebra.eighth_power u (hu 0) same sameFlip
      have inserted (t : Phase m) : Gadget.Realizes F .disequality
          (weighted (a*reps.multiplier true t*t.val) (weights t.val u)) :=
        insertion_actual positive F reps a u actualM t
      have scalar (t : Phase m) : a*reps.multiplier true t*t.val ≠ 0 :=
        mul_ne_zero (mul_ne_zero ha (reps.multiplier_ne_zero true t)) (t.property.ne_zero positive)
      have live (t : Phase m) : ∀ j, weights t.val u j ≠ 0 :=
        weights_nonzero t.val (t.property.ne_zero positive) u hu
      by_cases phaseDecks : ∀ t : Phase m, ∀ k : Fin 3,
          MonomialPhysicalDeck reps (row (a*reps.multiplier true t*t.val) (weights t.val u) k)
      · left
        refine ⟨eighth,?_⟩
        intro t ht
        let phase : Phase m := ⟨t,ht⟩
        have sameInserted := physical_decks_fourths hm F reps _ _ (scalar phase) (live phase)
          (phaseDecks phase)
        exact phase_fourth t (ht.ne_zero positive) u (hu 0) same sameInserted
      · push Not at phaseDecks
        obtain ⟨t,k,missing⟩ := phaseDecks
        obtain ⟨i,e,p,z,hn,ho,hr⟩ := escape_of_not_decks F hI reps _ _ (inserted t)
          (fun all => missing (all k))
        exact Or.inr (bad_of_line positive F reps _ hn ho hr
          (physical_card_parity F reps _ (onPorts_even _ _ _ _ _ _ _) e p z))
    · obtain ⟨i,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps c v actualFlip flipped
      exact Or.inr (bad_of_line positive F reps _ hn ho hr
        (physical_card_parity F reps _ (onPorts_even _ _ _ _ _ _ _) e p t))
  · obtain ⟨i,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps a u actualM original
    exact Or.inr (bad_of_line positive F reps _ hn ho hr
      (physical_card_parity F reps _ (onPorts_even _ _ _ _ _ _ _) e p t))

/-- All gauge rows, retained I, and EVERY monomial binary row use the same
basis. Its mandatory native-X condition is inherited, not replaced. -/
theorem family_with_binaries_or_bad {ι : Type} {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m)
    (a : ι → AlgebraicComplex) (u : ι → Fin 4 → AlgebraicComplex) (base : ι)
    (ha : ∀ i, a i ≠ 0) (hu : ∀ i j, u i j ≠ 0)
    (actual : ∀ i, Gadget.Realizes F .disequality (weighted (a i) (u i))) :
    IsCommonKBasis affineClass
      (rows a u ∪ {f | ∃ B : Mat, B∈groupM m ∧ f=⟨2,kernelSignature B⟩})
      (EightVertexGaugeAffine.diagonalBasis (u base 0) (hu base 0)) ∨ BadBinary F m := by
  rcases common_basis_or_physical_escape hm F hI reps a u base ha hu actual with basis | bad
  · rcases constraints_or_bad hm F hI reps (a base) (u base) (ha base) (hu base) (actual base) with
      ⟨eighth,phases⟩ | bad
    · exact Or.inl (EightVertexGaugeBinaryBasis.common_basis_with_binaries (rows a u)
        (u base 0) (hu base 0) eighth phases basis)
    · exact Or.inr bad
  · exact Or.inr bad

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePhaseInsertion
end
