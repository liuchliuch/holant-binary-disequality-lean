import Holant.Proofs.Algorithms.TransformRecognition.ExtensionAffine
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineNormalForm


namespace Holant.LocalDrafts.MainChain.TransformRecognition.ExtensionLocalAffine
open Holant.Tractable
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [Field E] (φ : AlgebraicComplex →+* E)

def twist {n : ℕ} (alpha : Fin n → Bool) (f : Signature E n) : Signature E n :=
  fun x => φ (LocalAffineTwists.phaseWeight alpha x) * f x

/-- Full tensor action by the source diagonal phases, including zero entries. -/
theorem twist_action {n : ℕ} (alpha : Fin n → Bool) (f : Signature E n) :
    Signature.coordinateAction
      (fun j a b => φ (localPhaseMatrix (alpha j) a b)) f=twist φ alpha f := by
  funext x
  unfold Signature.coordinateAction
  rw [Fintype.sum_eq_single x]
  · unfold twist LocalAffineTwists.phaseWeight
    rw [map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    cases ha : alpha j <;> cases hx : x j <;>
      simp [localPhaseMatrix,phaseMatrix,Signature.equality,ha,hx]
  · intro y hy
    have hn : ∃ j, x j ≠ y j := by
      by_contra h
      push_neg at h
      exact hy (funext (fun j => (h j).symm))
    obtain ⟨j,hj⟩ := hn
    have hz : (∏ k, φ (localPhaseMatrix (alpha k) (x k) (y k)))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      cases ha : alpha j <;> simp [localPhaseMatrix,phaseMatrix,Signature.equality,ha,hj]
    rw [hz,zero_mul]

def LocalAffineOver {n : ℕ} (f : Signature E n) : Prop :=
  ∀ alpha, f alpha ≠ 0 → ExtensionAffine.AffineOver φ (twist φ alpha f)

def Matches {n : ℕ} (B : LocalAffineNormalForm.Code n) (c : (Fin n → Bool) → E)
    (f : Signature E n) : Prop :=
  (∀ x, f x ≠ 0 ↔ x ∈ B.1) ∧ ∀ alpha ∈ B.1,
    twist φ alpha f=ExtensionAffine.formula φ (B.2 alpha) (c alpha)

theorem localAffine_iff {n : ℕ} (f : Signature E n) : LocalAffineOver φ f ↔
    ∃ B : LocalAffineNormalForm.Code n, ∃ c : (Fin n → Bool) → E, Matches φ B c f := by
  constructor
  · intro hf
    let masked (alpha : Fin n → Bool) : Signature E n :=
      if f alpha ≠ 0 then twist φ alpha f else 0
    have ha (alpha : Fin n → Bool) : ExtensionAffine.AffineOver φ (masked alpha) := by
      unfold masked
      split_ifs with h
      · exact hf alpha h
      · exact Or.inl rfl
    have hex := fun alpha => (ExtensionAffine.affine_iff φ _).mp (ha alpha)
    choose types scales he using hex
    refine ⟨(Finset.univ.filter (fun x => f x ≠ 0),types),scales,?_,?_⟩
    · intro x
      simp
    · intro alpha ha
      have hn : f alpha ≠ 0 := (Finset.mem_filter.mp ha).2
      simpa [masked,hn] using he alpha
  · rintro ⟨B,c,h⟩ alpha ha
    apply (ExtensionAffine.affine_iff φ _).mpr
    exact ⟨B.2 alpha,c alpha,h.2 alpha ((h.1 alpha).mp ha)⟩

theorem entry_constraints {n : ℕ} (B : LocalAffineNormalForm.Code n)
    (c : (Fin n → Bool) → E) (f : Signature E n) : Matches φ B c f ↔
    (∀ x ∈ B.1, f x ≠ 0) ∧ (∀ x, x ∉ B.1 → f x=0) ∧
      ∀ alpha ∈ B.1, ∀ x,
        φ (LocalAffineTwists.phaseWeight alpha x)*f x =
          c alpha*φ (ExtensionAffine.coefficient (B.2 alpha) x) := by
  constructor
  · intro h
    refine ⟨fun x hx => (h.1 x).mpr hx,?_,?_⟩
    · intro x hx
      by_contra hn
      exact hx ((h.1 x).mp hn)
    · intro alpha ha x
      exact congrFun (h.2 alpha ha) x
  · rintro ⟨hn,hz,he⟩
    constructor
    · intro x
      constructor
      · intro hx
        by_contra hm
        exact hx (hz x hm)
      · exact hn x
    · intro alpha ha
      exact funext (he alpha ha)

theorem twist_id {n : ℕ} (alpha : Fin n → Bool) (f : Signature AlgebraicComplex n) :
    twist (RingHom.id AlgebraicComplex) alpha f=localTwist alpha f := by
  funext x
  exact (LocalAffineTwists.localTwist_formula alpha f x).symm

theorem localAffine_id_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    LocalAffineOver (RingHom.id AlgebraicComplex) f ↔ LocalAffine f := by
  simp only [LocalAffineOver,LocalAffine,twist_id,ExtensionAffine.affine_id_iff]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.ExtensionLocalAffine
