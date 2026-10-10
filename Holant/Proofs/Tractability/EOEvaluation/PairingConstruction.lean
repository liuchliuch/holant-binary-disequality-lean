import Holant.Proofs.Tractability.EOEvaluation.PairingCharacters


namespace Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction
open Holant.Tractable Distribution PairingCharacters
open scoped BigOperators
noncomputable section
variable {n : ℕ} (D : Data n)

abbrev Side (b : Bool) := {j : Fin n // D.base.val j = b}
abbrev Fiber (k : Point D → Bool) (b : Bool) := {j : Fin n // key D j = k ∧ D.base.val j = b}

theorem indicator_count (k : Point D → Bool) (b : Bool) :
    (∑ j : Fin n, if key D j = k ∧ D.base.val j = b then (1 : ℚ) else 0) =
      Fintype.card (Fiber D k b) := by
  classical
  simp [Fiber, Fintype.card_subtype, Finset.sum_ite]

theorem fiber_card (k : Point D → Bool) : Fintype.card (Fiber D k false) = Fintype.card (Fiber D k true) := by
  classical
  have hi (j : Fin n) : (if key D j = k then spin (D.base.val j) else 0) =
      (if key D j = k ∧ D.base.val j = true then (1 : ℚ) else 0) -
      (if key D j = k ∧ D.base.val j = false then (1 : ℚ) else 0) := by
    by_cases h : key D j = k <;> cases hb : D.base.val j <;> simp [h, hb, spin]
  have h := fiber_balance D k
  simp only [hi, Finset.sum_sub_distrib, indicator_count] at h
  have he : (Fintype.card (Fiber D k false) : ℚ) = Fintype.card (Fiber D k true) := by linarith
  exact_mod_cast he

def flattenFiber (k : Point D → Bool) (b : Bool) :
    {j : Side D b // key D j.val = k} ≃ Fiber D k b where
  toFun j := ⟨j.val.val, j.property, j.val.property⟩
  invFun j := ⟨⟨j.val, j.property.2⟩, j.property.1⟩
  left_inv j := rfl
  right_inv j := rfl

def fiberEquiv (k : Point D → Bool) :
    {j : Side D false // key D j.val = k} ≃ {j : Side D true // key D j.val = k} :=
  (flattenFiber D k false).trans
    ((Fintype.equivOfCardEq (fiber_card D k)).trans (flattenFiber D k true).symm)

def matching : Side D false ≃ Side D true := Equiv.ofFiberEquiv (fiberEquiv D)

theorem matching_key (j : Side D false) : key D (matching D j).val = key D j.val :=
  Equiv.ofFiberEquiv_map (fiberEquiv D) j

theorem matching_opposite (j : Side D false) (x : Point D) : x.val j.val ≠ x.val (matching D j).val := by
  have hk := congrFun (matching_key D j) x
  have h0 := j.property
  have h1 := (matching D j).property
  dsimp [key] at hk
  rw [h0, h1] at hk
  cases hx : x.val j.val <;> cases hy : x.val (matching D j).val <;> simp_all

def pairedSum : (Side D false × Bool) ≃ (Side D false ⊕ Side D true) where
  toFun p := if p.2 then .inr (matching D p.1) else .inl p.1
  invFun p := match p with
    | .inl j => (j, false)
    | .inr j => ((matching D).symm j, true)
  left_inv p := by rcases p with ⟨j, b⟩; cases b <;> simp
  right_inv p := by cases p <;> simp

def joinSides : (Side D false ⊕ Side D true) ≃ Fin n where
  toFun p := p.elim Subtype.val Subtype.val
  invFun j := if h : D.base.val j = false then .inl ⟨j, h⟩
    else .inr ⟨j, by cases hb : D.base.val j <;> simp_all⟩
  left_inv p := by
    rcases p with j | j
    · simp [j.property]
    · have hn : D.base.val j.val ≠ false := by simp [j.property]
      simp [hn]
  right_inv j := by dsimp; split_ifs <;> rfl

def pairing : OrientedPerfectPairing n where
  count := Fintype.card (Side D false)
  ports := ((Equiv.prodCongr (Fintype.equivFin (Side D false)).symm (Equiv.refl Bool)).trans
    (pairedSum D)).trans (joinSides D)

@[simp] theorem port_false (j : Fin (pairing D).count) :
    (pairing D).ports (j, false) = ((Fintype.equivFin (Side D false)).symm j).val := rfl
@[simp] theorem port_true (j : Fin (pairing D).count) :
    (pairing D).ports (j, true) = (matching D ((Fintype.equivFin (Side D false)).symm j)).val := rfl

theorem covers (x : Word n) (hx : x ∈ D.points) (j : Fin (pairing D).count) :
    x ((pairing D).ports (j, false)) ≠ x ((pairing D).ports (j, true)) := by
  exact matching_opposite D ((Fintype.equivFin (Side D false)).symm j) ⟨x, hx⟩

theorem twice_count : 2 * (pairing D).count = n := by
  have h := Fintype.card_congr (pairing D).ports
  simpa [Fintype.card_prod, Nat.mul_comm] using h

end
end Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction
