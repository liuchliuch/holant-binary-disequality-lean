import Holant.Platonic.RainbowLocalization.Source
import Holant.Platonic.RainbowLocalization.PhysicalCards
import Holant.Platonic.RainbowLocalization.ClosingKernels

/-! The exact original-port closure collection retaining the marked pair
and the four localized ports. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure MatchingCut
open scoped BigOperators
variable {P S V Q E : Type*}

def splitCutPorts (s : P → Bool) : Side s true ⊕ Side s false ≃ P where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun p := if h : s p = true then .inl ⟨p,h⟩ else .inr ⟨p,by cases hp : s p <;> simp_all⟩
  left_inv p := by
    cases p with
    | inl p => simp [p.property]
    | inr p => simp [p.property]
  right_inv p := by dsimp; split <;> rfl

def fullClosurePorts (p : Bool ⊕ P ≃ V) (r : CollectionPorts P S E) (o : Bool ⊕ S ≃ Q) :
    CollectionPorts V Q E :=
  (Equiv.sumCongr o.symm (Equiv.refl (E × Bool))).trans
    ((Equiv.sumAssoc Bool S (E × Bool)).trans ((Equiv.sumCongr (Equiv.refl Bool) r).trans p))

@[simp] theorem fullClosurePorts_pair (p : Bool ⊕ P ≃ V) (r : CollectionPorts P S E)
    (o : Bool ⊕ S ≃ Q) (t : Bool) :
    fullClosurePorts p r o (.inl (o (.inl t))) = p (.inl t) := by simp [fullClosurePorts]

@[simp] theorem fullClosurePorts_boundary (p : Bool ⊕ P ≃ V) (r : CollectionPorts P S E)
    (o : Bool ⊕ S ≃ Q) (q : S) :
    fullClosurePorts p r o (.inl (o (.inr q))) = p (.inr (r (.inl q))) := by simp [fullClosurePorts]

@[simp] theorem fullClosurePorts_edge (p : Bool ⊕ P ≃ V) (r : CollectionPorts P S E)
    (o : Bool ⊕ S ≃ Q) (e : E) (t : Bool) :
    fullClosurePorts p r o (.inr (e,t)) = p (.inr (r (.inr (e,t)))) := rfl

theorem full_assignment [DecidableEq E] [DecidableEq V] [DecidableEq Q]
    (p : Bool ⊕ P ≃ V) (r : CollectionPorts P S E)
    (o : Bool ⊕ S ≃ Q) (x : S → Bool) (y : E → Bool × Bool) (a b : Bool) :
    collectionAssignment (fullClosurePorts p r o) (pairAssignment o a b x) y =
      pairAssignment p a b (collectionAssignment r x y) := by
  funext i
  obtain ⟨z,rfl⟩ := p.surjective i
  cases z with
  | inl t =>
    have hh := collectionAssignment_boundary (fullClosurePorts p r o) (pairAssignment o a b x) y (o (.inl t))
    simpa only [fullClosurePorts_pair,pairAssignment_pair] using hh
  | inr z =>
    obtain ⟨z,rfl⟩ := r.surjective z
    cases z with
    | inl q =>
      have hh := collectionAssignment_boundary (fullClosurePorts p r o) (pairAssignment o a b x) y (o (.inr q))
      simpa only [fullClosurePorts_boundary,pairAssignment_rest,collectionAssignment_boundary] using hh
    | inr et =>
      rcases et with ⟨e,t⟩
      have hh := collectionAssignment_edge (fullClosurePorts p r o) (pairAssignment o a b x) y e t
      simpa only [fullClosurePorts_edge,pairAssignment_rest,collectionAssignment_edge] using hh

/-- The marked card map itself commutes with the constructed closure,
with both original and output ordered-port records retained. -/
theorem cardMap_full_closure [Fintype E] [DecidableEq E]
    [DecidableEq P] [DecidableEq V] [DecidableEq Q]
    (p : Bool ⊕ P ≃ V) (r : CollectionPorts P S E) (o : Bool ⊕ S ≃ Q)
    (C : E → Kernel ℂ) (f : Tensor ℂ V) (K : Kernel ℂ) :
    cardMap o (contractCollection (fullClosurePorts p r o) C f) K =
      contractCollection r C (cardMap p f K) := by
  funext x
  simp only [cardMap,LinearMap.coe_mk,AddHom.coe_mk,contractCollection,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Bool))
    (t := (Finset.univ : Finset (E → Bool × Bool)))]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [full_assignment]
  ring

variable [Fintype P] [DecidableEq P]
variable {D₀ D₁ D₂ : Presentation ℂ P}

def localizedPorts (L : AlgebraicLocalization D₀ D₁ D₂) :
    CollectionPorts P (Side (cut L.ports) true) (Fin L.common.edges) :=
  (Equiv.sumCongr (Equiv.refl _) L.common.ports).trans (splitCutPorts (cut L.ports))

@[simp] theorem localizedPorts_boundary (L : AlgebraicLocalization D₀ D₁ D₂)
    (q : Side (cut L.ports) true) : localizedPorts L (.inl q) = q.val := rfl

@[simp] theorem localizedPorts_edge (L : AlgebraicLocalization D₀ D₁ D₂)
    (e : Fin L.common.edges) (b : Bool) :
    localizedPorts L (.inr (e,b)) = (L.common.ports (e,b)).val := rfl

def sixPortOrder (L : AlgebraicLocalization D₀ D₁ D₂) : Bool ⊕ Side (cut L.ports) true ≃ Fin 6 :=
  (Equiv.sumCongr finTwoEquiv.symm
    (Fintype.equivFinOfCardEq ((side_cut_card L.ports).trans L.card_ports))).trans finSumFinEquiv

@[simp] theorem sixPortOrder_false (L : AlgebraicLocalization D₀ D₁ D₂) :
    sixPortOrder L (.inl false) = 0 := rfl

@[simp] theorem sixPortOrder_true (L : AlgebraicLocalization D₀ D₁ D₂) :
    sixPortOrder L (.inl true) = 1 := rfl

def originalClosurePorts {n : ℕ} (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n) :
    CollectionPorts (Fin n) (Fin 6) (Fin L.common.edges) :=
  fullClosurePorts p (localizedPorts L) (sixPortOrder L)

@[simp] theorem originalClosurePorts_zero {n : ℕ} (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) : originalClosurePorts L p (.inl 0) = p (.inl false) :=
  fullClosurePorts_pair p (localizedPorts L) (sixPortOrder L) false

@[simp] theorem originalClosurePorts_one {n : ℕ} (L : AlgebraicLocalization D₀ D₁ D₂)
    (p : Bool ⊕ P ≃ Fin n) : originalClosurePorts L p (.inl 1) = p (.inl true) :=
  fullClosurePorts_pair p (localizedPorts L) (sixPortOrder L) true

theorem original_kernel_count {n : ℕ} (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n) :
    L.common.edges = (n - 6) / 2 := by
  have hp := Fintype.card_congr p
  simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at hp
  exact L.common_edges_for_card_map n (by omega)

theorem localized_assignment_boundary (L : AlgebraicLocalization D₀ D₁ D₂)
    (x : Side (cut L.ports) true → Bool) (y : Fin L.common.edges → Bool × Bool)
    (q : Side (cut L.ports) true) : collectionAssignment (localizedPorts L) x y q.val = x q :=
  collectionAssignment_boundary (localizedPorts L) x y q

theorem localized_assignment_common (L : AlgebraicLocalization D₀ D₁ D₂)
    (x : Side (cut L.ports) true → Bool) (y : Fin L.common.edges → Bool × Bool)
    (e : Fin L.common.edges) (b : Bool) :
    collectionAssignment (localizedPorts L) x y (L.common.ports (e,b)).val =
      if b then (y e).2 else (y e).1 :=
  collectionAssignment_edge (localizedPorts L) x y e b

theorem common_tensor_assignment (L : AlgebraicLocalization D₀ D₁ D₂)
    (x : Side (cut L.ports) true → Bool) (y : Fin L.common.edges → Bool × Bool) :
    L.common.tensor (fun q => collectionAssignment (localizedPorts L) x y q.val) =
      L.common.scalar * ∏ e, L.common.matrix e (y e).1 (y e).2 := by
  unfold Presentation.tensor productValue
  simp only [localized_assignment_common,Bool.false_eq_true,ite_false,ite_true]

def closureScale (L : AlgebraicLocalization D₀ D₁ D₂) (C : Fin L.common.edges → Kernel ℂ) : ℂ :=
  L.common.scalar * ∏ e, Kernel.pair (C e) (L.common.matrix e)

/-- Closing the literal common matching product preserves every factorized
card with the same exact scalar. -/
theorem close_factorized (L : AlgebraicLocalization D₀ D₁ D₂)
    (C : Fin L.common.edges → Kernel ℂ) (F : Tensor ℂ P)
    (q : Tensor ℂ (Side (cut L.ports) true))
    (hF : ∀ x, F x = q (fun p => x p.val) * L.common.tensor (fun p => x p.val)) :
    contractCollection (localizedPorts L) C F = closureScale L C • q := by
  funext x
  have hterm (y : Fin L.common.edges → Bool × Bool) :
      kernelProduct C y * F (collectionAssignment (localizedPorts L) x y) =
      L.common.scalar * ((∏ e, C e (y e).1 (y e).2) *
        (∏ e, L.common.matrix e (y e).1 (y e).2) * q x) := by
    rw [hF,common_tensor_assignment]
    have hx : (fun p => collectionAssignment (localizedPorts L) x y p.val) = x :=
      funext (localized_assignment_boundary L x y)
    rw [hx]
    unfold kernelProduct
    ring
  simp only [contractCollection,Pi.smul_apply,smul_eq_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum,closing_product_identity]
  simp only [closureScale,mul_assoc]

end Holant.Platonic.RainbowLocalization.Physical
