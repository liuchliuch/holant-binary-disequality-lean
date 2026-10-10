import Holant.Platonic.RainbowLocalization.PhysicalCommutation
import Holant.Platonic.FixedMatchingRuling.Reconstruction

/-! Literal bilinear cards at a recorded ordered original pair, with the
remaining original ports explicitly identified. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
variable {P Q : Type*} [DecidableEq P]

def pairAssignment (p : Bool ⊕ Q ≃ P) (a b : Bool) (x : Q → Bool) : P → Bool :=
  fun i => Sum.elim (fun t => if t then b else a) x (p.symm i)

@[simp] theorem pairAssignment_pair (p : Bool ⊕ Q ≃ P) (a b t : Bool) (x : Q → Bool) :
    pairAssignment p a b x (p (.inl t)) = if t then b else a := by simp [pairAssignment]

@[simp] theorem pairAssignment_rest (p : Bool ⊕ Q ≃ P) (a b : Bool) (x : Q → Bool) (q : Q) :
    pairAssignment p a b x (p (.inr q)) = x q := by simp [pairAssignment]

def cardMap (p : Bool ⊕ Q ≃ P) (f : Tensor ℂ P) : Kernel ℂ →ₗ[ℂ] Tensor ℂ Q where
  toFun K x := ∑ a : Bool, ∑ b : Bool, K a b * f (pairAssignment p a b x)
  map_add' K L := by funext x; simp [add_mul,Finset.sum_add_distrib]
  map_smul' c K := by funext x; simp [mul_assoc,mul_add]

theorem cardMap_smul_tensor (p : Bool ⊕ Q ≃ P) (f : Tensor ℂ P) (c : ℂ) (K : Kernel ℂ) :
    cardMap p (c • f) K = c • cardMap p f K := by
  funext x
  simp only [cardMap,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

@[simp] theorem cardMap_zero_tensor (p : Bool ⊕ Q ≃ P) (K : Kernel ℂ) :
    cardMap p (0 : Tensor ℂ P) K = 0 := by
  funext x
  simp [cardMap]

/-- This is the same literal coefficient card map used by fixed-matching
reconstruction, specialized to its block-port assignment coordinates. -/
theorem cardMap_reconstruction_coefficients {M : Type*} [Fintype M]
    (ℓ : M → ℕ) (p : Bool ⊕ ((e : M) × Fin (ℓ e)) ≃ P) (f : Tensor ℂ P)
    (K : Kernel ℂ) (x : (e : M) → Fin (ℓ e) → Bool) :
    cardMap p f K (fun q => x q.1 q.2) =
      FixedMatchingRuling.Physical.cardCoefficients ℓ p f K x := rfl

def pairRemaining (p : Bool ⊕ Q ≃ P) : Q ≃ Remaining (p (.inl false)) (p (.inl true)) :=
  Equiv.ofBijective (fun q => (⟨p (.inr q),by
    constructor <;> intro h <;> cases p.injective h⟩ : Remaining (p (.inl false)) (p (.inl true)))) (by
    constructor
    · intro q r h
      exact Sum.inr.inj (p.injective (congrArg Subtype.val h))
    · intro q
      obtain ⟨t,ht⟩ := p.surjective q.val
      cases t with
      | inr r => exact ⟨r,Subtype.ext ht⟩
      | inl b =>
        cases b
        · exact (q.property.1 ht.symm).elim
        · exact (q.property.2 ht.symm).elim)

@[simp] theorem pairRemaining_val (p : Bool ⊕ Q ≃ P) (q : Q) : (pairRemaining p q).val = p (.inr q) := rfl

theorem pair_distinct (p : Bool ⊕ Q ≃ P) : p (.inl false) ≠ p (.inl true) := by
  intro h
  have hh := Sum.inl.inj (p.injective h)
  cases hh

theorem pairAssignment_eq_insert (p : Bool ⊕ Q ≃ P) (a b : Bool) (x : Q → Bool) :
    pairAssignment p a b x =
      insertPair (p (.inl false)) (p (.inl true)) a b
        (extendRemaining _ _ (fun q => x ((pairRemaining p).symm q))) := by
  funext i
  obtain ⟨t,rfl⟩ := p.surjective i
  cases t with
  | inl t =>
    cases t
    · rw [pairAssignment_pair,insertPair_first (pair_distinct p)]; rfl
    · rw [pairAssignment_pair,insertPair_second]; rfl
  | inr q =>
    rw [pairAssignment_rest,insertPair_other]
    · change x q = extendRemaining _ _ (fun q => x ((pairRemaining p).symm q)) (pairRemaining p q).val
      rw [extendRemaining_apply,Equiv.symm_apply_apply]
    · intro h; cases p.injective h
    · intro h; cases p.injective h

/-- The coordinate card is the existing original-port `contractPair`, with
only its surviving port names reindexed. -/
theorem cardMap_eq_contractPair (p : Bool ⊕ Q ≃ P) (f : Tensor ℂ P) (K : Kernel ℂ) :
    cardMap p f K = Tensor.reindex (pairRemaining p).symm
      (contractPair (p (.inl false)) (p (.inl true)) K f) := by
  funext x
  simp only [cardMap,LinearMap.coe_mk,AddHom.coe_mk,Tensor.reindex,contractPair,
    pairAssignment_eq_insert]

/-- Collinearity of actual domain kernels passes through the literal card
map, so algebraic localization need not assume collinearity of its outputs. -/
theorem card_line_from_domain (p : Bool ⊕ Q ≃ P) (f : Tensor ℂ P) (K₀ K₁ K₂ : Kernel ℂ)
    (hline : K₂ ∈ Submodule.span ℂ ({K₀,K₁} : Set (Kernel ℂ))) :
    cardMap p f K₂ ∈ Submodule.span ℂ ({cardMap p f K₀,cardMap p f K₁} : Set (Tensor ℂ Q)) := by
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hline
  apply Submodule.mem_span_pair.mpr
  refine ⟨a,b,?_⟩
  rw [← map_smul,← map_smul,← map_add,he]

end Holant.Platonic.RainbowLocalization.Physical
