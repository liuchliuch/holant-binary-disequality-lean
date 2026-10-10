import Holant.Pauli.ExoticKlein.AlternatingOrbits
import Holant.Certificates.MatchingContractionClosure.NonzeroProducts
import Mathlib.Logic.Equiv.Functor

/-! Canonical cut coordinates for an actual oriented perfect matching.
The crossing and internal edges are computed from the original port cut;
no factorization or rank statement is included in the coordinate data.
-/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein
open scoped BigOperators
variable {P : Type*} {r : ℕ}

namespace MatchingCut

abbrev Side (s : P → Bool) (b : Bool) := {p : P // s p = b}

abbrev Internal (M : Matching P r) (s : P → Bool) (b : Bool) :=
  {e : Fin r // s (M.ports (e, false)) = b ∧ s (M.ports (e, true)) = b}

abbrev Crossing (M : Matching P r) (s : P → Bool) :=
  {e : Fin r // s (M.ports (e, false)) ≠ s (M.ports (e, true))}

/-- The endpoint of a crossing edge that lies on the specified side. -/
def crossingEnd (M : Matching P r) (s : P → Bool) (b : Bool)
    (e : Crossing M s) : Bool := if s (M.ports (e.val, false)) = b then false else true

theorem crossingEnd_side (M : Matching P r) (s : P → Bool) (b : Bool)
    (e : Crossing M s) : s (M.ports (e.val, crossingEnd M s b e)) = b := by
  have he := e.property
  cases h₀ : s (M.ports (e.val, false)) <;>
    cases h₁ : s (M.ports (e.val, true)) <;> cases b <;>
      simp_all [crossingEnd]

theorem crossingEnd_unique (M : Matching P r) (s : P → Bool) (b : Bool)
    (e : Crossing M s) (t : Bool) (ht : s (M.ports (e.val, t)) = b) :
    crossingEnd M s b e = t := by
  have he := e.property
  cases h₀ : s (M.ports (e.val, false)) <;>
    cases h₁ : s (M.ports (e.val, true)) <;> cases b <;> cases t <;>
      simp_all [crossingEnd]

def sidePort (M : Matching P r) (s : P → Bool) (b : Bool) :
    (Internal M s b × Bool) ⊕ Crossing M s → Side s b
  | .inl (e, t) => ⟨M.ports (e.val, t), by cases t; exact e.property.1; exact e.property.2⟩
  | .inr e => ⟨M.ports (e.val, crossingEnd M s b e), crossingEnd_side M s b e⟩

theorem sidePort_injective (M : Matching P r) (s : P → Bool) (b : Bool) :
    Function.Injective (sidePort M s b) := by
  intro x y h
  have hh := congrArg (fun p : Side s b => M.ports.symm p.val) h
  cases x with
  | inl x =>
    rcases x with ⟨e,t⟩
    cases y with
    | inl y =>
      rcases y with ⟨f,u⟩
      simp only [sidePort, Equiv.symm_apply_apply] at hh
      have he : e = f := Subtype.ext (congrArg Prod.fst hh)
      have ht : t = u := congrArg Prod.snd hh
      subst f; subst u; rfl
    | inr f =>
      simp only [sidePort, Equiv.symm_apply_apply] at hh
      have he : e.val = f.val := congrArg Prod.fst hh
      have hsame := e.property.1.trans e.property.2.symm
      rw [he] at hsame
      exact (f.property hsame).elim
  | inr e =>
    cases y with
    | inl y =>
      rcases y with ⟨f,u⟩
      simp only [sidePort, Equiv.symm_apply_apply] at hh
      have he : e.val = f.val := congrArg Prod.fst hh
      have hsame := f.property.1.trans f.property.2.symm
      rw [← he] at hsame
      exact (e.property hsame).elim
    | inr f =>
      simp only [sidePort, Equiv.symm_apply_apply] at hh
      have he : e = f := Subtype.ext (congrArg Prod.fst hh)
      rw [he]

theorem sidePort_surjective (M : Matching P r) (s : P → Bool) (b : Bool) :
    Function.Surjective (sidePort M s b) := by
  intro p
  obtain ⟨⟨e,t⟩, he⟩ := M.ports.surjective p.val
  have ht : s (M.ports (e,t)) = b := he ▸ p.property
  by_cases hc : s (M.ports (e,false)) ≠ s (M.ports (e,true))
  · let c : Crossing M s := ⟨e,hc⟩
    refine ⟨.inr c, Subtype.ext ?_⟩
    change M.ports (e, crossingEnd M s b c) = p.val
    rw [crossingEnd_unique M s b c t ht]
    exact he
  · have hs : s (M.ports (e,false)) = s (M.ports (e,true)) := not_not.mp hc
    have hi : s (M.ports (e,false)) = b ∧ s (M.ports (e,true)) = b := by
      cases t
      · exact ⟨ht, hs.symm.trans ht⟩
      · exact ⟨hs.trans ht, ht⟩
    exact ⟨.inl (⟨e,hi⟩,t), Subtype.ext he⟩

/-- A side of a cut consists exactly of both ports of its internal edges and
one port from every crossing edge. -/
def sidePorts (M : Matching P r) (s : P → Bool) (b : Bool) :
    (Internal M s b × Bool) ⊕ Crossing M s ≃ Side s b :=
  Equiv.ofBijective (sidePort M s b)
    ⟨sidePort_injective M s b, sidePort_surjective M s b⟩

/-- Reordering the actual cut assignments into internal bits and crossing bits. -/
def sideAssignments (M : Matching P r) (s : P → Bool) (b : Bool) :
    (Side s b → Bool) ≃ (((Internal M s b × Bool) → Bool) × (Crossing M s → Bool)) where
  toFun x := (fun et => x (sidePorts M s b (.inl et)),
    fun e => x (sidePorts M s b (.inr e)))
  invFun x p := Sum.elim x.1 x.2 ((sidePorts M s b).symm p)
  left_inv x := by
    funext p
    obtain ⟨et, rfl⟩ := (sidePorts M s b).surjective p
    cases et <;> simp
  right_inv x := by
    rcases x with ⟨x,y⟩
    apply Prod.ext <;> funext e <;> simp

@[simp] theorem sideAssignments_symm_internal (M : Matching P r) (s : P → Bool) (b : Bool)
    (x : ((Internal M s b × Bool) → Bool) × (Crossing M s → Bool))
    (e : Internal M s b) (t : Bool) :
    (sideAssignments M s b).symm x (sidePorts M s b (.inl (e,t))) = x.1 (e,t) := by
  simp [sideAssignments]

@[simp] theorem sideAssignments_symm_crossing (M : Matching P r) (s : P → Bool) (b : Bool)
    (x : ((Internal M s b × Bool) → Bool) × (Crossing M s → Bool))
    (e : Crossing M s) :
    (sideAssignments M s b).symm x (sidePorts M s b (.inr e)) = x.2 e := by
  simp [sideAssignments]

/-- The parity fact used on an even component cut follows from the literal
port decomposition, without a graph-theoretic parity assumption. -/
theorem side_card [Fintype P] (M : Matching P r) (s : P → Bool) (b : Bool) :
    Fintype.card (Side s b) =
      2 * Fintype.card (Internal M s b) + Fintype.card (Crossing M s) := by
  have he := Fintype.card_congr (sidePorts M s b)
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, mul_comm] using he.symm

private def edgePart (M : Matching P r) (s : P → Bool) :
    (Internal M s true ⊕ Internal M s false) ⊕ Crossing M s → Fin r
  | .inl (.inl e) => e.val
  | .inl (.inr e) => e.val
  | .inr e => e.val

/-- All original edges, partitioned by their actual positions relative to the cut. -/
def edgeParts (M : Matching P r) (s : P → Bool) :
    (Internal M s true ⊕ Internal M s false) ⊕ Crossing M s ≃ Fin r :=
  Equiv.ofBijective (edgePart M s) (by
    constructor
    · intro x y h
      rcases x with ((⟨e,he⟩ | ⟨e,he⟩) | ⟨e,he⟩) <;>
        rcases y with ((⟨f,hf⟩ | ⟨f,hf⟩) | ⟨f,hf⟩)
      all_goals dsimp only [edgePart] at h
      all_goals subst f
      all_goals simp_all
      all_goals first
        | exact hf (he.1.trans he.2.symm)
        | exact he (hf.1.trans hf.2.symm)
        | exact Bool.noConfusion (he.1.symm.trans hf.1)
    · intro e
      cases h₀ : s (M.ports (e,false)) <;> cases h₁ : s (M.ports (e,true))
      · exact ⟨.inl (.inr ⟨e,h₀,h₁⟩),rfl⟩
      · exact ⟨.inr ⟨e,by simp [h₀,h₁]⟩,rfl⟩
      · exact ⟨.inr ⟨e,by simp [h₀,h₁]⟩,rfl⟩
      · exact ⟨.inl (.inl ⟨e,h₀,h₁⟩),rfl⟩)

theorem prod_edgeParts {K : Type*} [CommMonoid K]
    (M : Matching P r) (s : P → Bool) (f : Fin r → K) :
    ∏ e, f e = ((∏ e : Internal M s true, f e.val) *
      ∏ e : Internal M s false, f e.val) * ∏ e : Crossing M s, f e.val := by
  have he := (edgeParts M s).prod_comp f
  change (∏ x, f (edgePart M s x)) = ∏ e, f e at he
  simpa only [Fintype.prod_sum_type, edgePart] using he.symm

/-- Join assignments to the two actual port subsets. -/
def joinAssignment (s : P → Bool) (x : Side s true → Bool) (y : Side s false → Bool) :
    P → Bool := fun p => if h : s p = true then x ⟨p,h⟩ else
      y ⟨p,by cases hp : s p <;> simp_all⟩

@[simp] theorem joinAssignment_true (s : P → Bool) (x : Side s true → Bool)
    (y : Side s false → Bool) (p : Side s true) : joinAssignment s x y p.val = x p := by
  simp [joinAssignment,p.property]

@[simp] theorem joinAssignment_false (s : P → Bool) (x : Side s true → Bool)
    (y : Side s false → Bool) (p : Side s false) : joinAssignment s x y p.val = y p := by
  simp [joinAssignment,p.property]

/-- The actual cut flattening, before any matching-coordinate permutation. -/
def flatten {K : Type*} (s : P → Bool) (F : Tensor K P) :
    Matrix (Side s true → Bool) (Side s false → Bool) K :=
  fun x y => F (joinAssignment s x y)

abbrev Words (M : Matching P r) (s : P → Bool) (b : Bool) :=
  ((Internal M s b × Bool) → Bool) × (Crossing M s → Bool)

def assignment (M : Matching P r) (s : P → Bool)
    (x : Words M s true) (y : Words M s false) : P → Bool :=
  joinAssignment s ((sideAssignments M s true).symm x) ((sideAssignments M s false).symm y)

theorem assignment_internal_true (M : Matching P r) (s : P → Bool)
    (x : Words M s true) (y : Words M s false)
    (e : Internal M s true) (t : Bool) : assignment M s x y (M.ports (e.val,t)) = x.1 (e,t) := by
  have h := joinAssignment_true s ((sideAssignments M s true).symm x)
    ((sideAssignments M s false).symm y) (sidePorts M s true (.inl (e,t)))
  rw [sideAssignments_symm_internal] at h
  exact h

theorem assignment_internal_false (M : Matching P r) (s : P → Bool)
    (x : Words M s true) (y : Words M s false)
    (e : Internal M s false) (t : Bool) : assignment M s x y (M.ports (e.val,t)) = y.1 (e,t) := by
  have h := joinAssignment_false s ((sideAssignments M s true).symm x)
    ((sideAssignments M s false).symm y) (sidePorts M s false (.inl (e,t)))
  rw [sideAssignments_symm_internal] at h
  exact h

theorem assignment_crossing_true (M : Matching P r) (s : P → Bool)
    (x : Words M s true) (y : Words M s false) (e : Crossing M s) :
    assignment M s x y (M.ports (e.val,crossingEnd M s true e)) = x.2 e := by
  have h := joinAssignment_true s ((sideAssignments M s true).symm x)
    ((sideAssignments M s false).symm y) (sidePorts M s true (.inr e))
  rw [sideAssignments_symm_crossing] at h
  exact h

theorem assignment_crossing_false (M : Matching P r) (s : P → Bool)
    (x : Words M s true) (y : Words M s false) (e : Crossing M s) :
    assignment M s x y (M.ports (e.val,crossingEnd M s false e)) = y.2 e := by
  have h := joinAssignment_false s ((sideAssignments M s true).symm x)
    ((sideAssignments M s false).symm y) (sidePorts M s false (.inr e))
  rw [sideAssignments_symm_crossing] at h
  exact h

def crossingMatrix {K : Type*} (M : Matching P r) (s : P → Bool)
    (A : Fin r → Matrix Bool Bool K) (e : Crossing M s) : Matrix Bool Bool K :=
  if s (M.ports (e.val,false)) then A e.val else (A e.val).transpose

theorem assignment_crossing_entry {K : Type*} (M : Matching P r) (s : P → Bool)
    (A : Fin r → Matrix Bool Bool K) (x : Words M s true) (y : Words M s false)
    (e : Crossing M s) :
    A e.val (assignment M s x y (M.ports (e.val,false)))
      (assignment M s x y (M.ports (e.val,true))) = crossingMatrix M s A e (x.2 e) (y.2 e) := by
  have hl := assignment_crossing_true M s x y e
  have hr := assignment_crossing_false M s x y e
  cases h₀ : s (M.ports (e.val,false)) <;>
    simp only [crossingEnd, h₀, Bool.false_eq_true, Bool.true_eq_false,
      ite_true, ite_false] at hl hr
  · simp only [crossingMatrix,h₀, Bool.false_eq_true, ite_false, Matrix.transpose_apply,hl,hr]
  · simp only [crossingMatrix,h₀, ite_true,hl,hr]

/-- The literal matching product factors in the computed cut coordinates. -/
theorem product_assignment {K : Type*} [Field K]
    (M : Matching P r) (s : P → Bool) (A : Fin r → Matrix Bool Bool K) (c : K)
    (x : Words M s true) (y : Words M s false) :
    Certificates.MatchingContractionClosure.productValue M.ports A c (assignment M s x y) =
      (c * ∏ e : Internal M s true, A e.val (x.1 (e,false)) (x.1 (e,true))) *
      (∏ e : Crossing M s, crossingMatrix M s A e (x.2 e) (y.2 e)) *
      (∏ e : Internal M s false, A e.val (y.1 (e,false)) (y.1 (e,true))) := by
  unfold Certificates.MatchingContractionClosure.productValue
  rw [prod_edgeParts M s]
  simp_rw [assignment_internal_true, assignment_internal_false, assignment_crossing_entry]
  ring

end MatchingCut
end Holant.Platonic.RainbowLocalization
