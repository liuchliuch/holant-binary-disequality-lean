import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhasePinCompose
import Mathlib.Algebra.BigOperators.Fin

/-! Finite blocks consist exclusively of signed substitutions into one
original signature. Their charge and phase value are literal finite
sums and products, with all pinned-coordinate constants retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlock
open Holant Holant.Tractable
open scoped BigOperators
namespace R
export NoIPurePhaseRecipeFactor (Port word incidence factor total)
end R
namespace P
export NoIPurePhasePinCompose (PurePins substitute compose fixedWeight)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n m l k : ℕ}

structure Block (n m : ℕ) where
  count : ℕ
  ports : Fin count → Fin n → R.Port m

def value {K : Type} [CommMonoid K] (f : Signature K n) (B : Block n m) :
    Signature K m := fun z => ∏ i, f (R.word (B.ports i) z)

def charge (B : Block n m) : Fin m → ℤ := R.total B.ports

def phase (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n m) : Signature AlgebraicComplex m :=
  fun z => ∏ i, r ^ weight (R.word (B.ports i) z) * f (R.word (B.ports i) z)

theorem phase_value (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n m) (z : (Fin m → Bool)) :
    phase r f B z = value f B z * R.factor B.ports r z := by
  simp only [phase, value, R.factor, Finset.prod_mul_distrib]
  exact mul_comm _ _

theorem phase_formula (r : AlgebraicComplex) (rn : r ≠ 0)
    (f : Signature AlgebraicComplex n) (B : Block n m) (z : (Fin m → Bool)) :
    phase r f B z = value f B z *
      (R.factor B.ports r (fun _ => false) * ∏ j, if z j then r ^ charge B j else 1) := by
  rw [phase_value, NoIPurePhaseRecipeFactor.formula B.ports r rn]
  rfl

theorem phase_affine_iff (r : AlgebraicComplex) (rn : r ≠ 0) (root : r ^ 16 = 1)
    (f : Signature AlgebraicComplex n) (B : Block n m)
    (zero : ∀ j, charge B j % 4 = 0) :
    Affine (phase r f B) ↔ Affine (value f B) := by
  have eqn : phase r f B = fun z => value f B z * R.factor B.ports r z :=
    funext (phase_value r f B)
  rw [eqn]
  exact NoIPurePhaseRecipeFactor.mul_iff B.ports r rn root zero (value f B)

def single (p : Fin n → R.Port m) : Block n m := ⟨1, fun _ => p⟩

@[simp] theorem value_single {K : Type} [CommMonoid K] (f : Signature K n)
    (p : Fin n → R.Port m) (z : (Fin m → Bool)) : value f (single p) z = f (R.word p z) := by
  simp [value, single]

@[simp] theorem charge_single (p : Fin n → R.Port m) (j : Fin m) :
    charge (single p) j = R.incidence p j := by simp [charge, R.total, single]

@[simp] theorem phase_single (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (p : Fin n → R.Port m) (z : (Fin m → Bool)) :
    phase r f (single p) z = r ^ weight (R.word p z) * f (R.word p z) := by
  simp [phase, single]

def append (B C : Block n m) : Block n m :=
  ⟨B.count + C.count, Fin.addCases B.ports C.ports⟩

theorem value_append {K : Type} [CommMonoid K] (f : Signature K n)
    (B C : Block n m) (z : (Fin m → Bool)) :
    value f (append B C) z = value f B z * value f C z := by
  simp [value, append, Fin.prod_univ_add]

theorem charge_append (B C : Block n m) (j : Fin m) :
    charge (append B C) j = charge B j + charge C j := by
  simp [charge, R.total, append, Fin.sum_univ_add]

theorem phase_append (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B C : Block n m) (z : (Fin m → Bool)) :
    phase r f (append B C) z = phase r f B z * phase r f C z := by
  simp [phase, append, Fin.prod_univ_add]

/-- The copy counts may differ among the blocks. -/
def flatten (Bs : Fin k → Block n m) : Block n m where
  count := ∑ i, (Bs i).count
  ports i :=
    let ix : (j : Fin k) × Fin (Bs j).count := finSigmaFinEquiv.symm i
    (Bs ix.1).ports ix.2

theorem value_flatten {K : Type} [CommMonoid K] (f : Signature K n)
    (Bs : Fin k → Block n m) (z : (Fin m → Bool)) :
    value f (flatten Bs) z = ∏ i, value f (Bs i) z := by
  let g : ((i : Fin k) × Fin (Bs i).count) → K :=
    fun ix => f (R.word ((Bs ix.1).ports ix.2) z)
  change (∏ i, g (finSigmaFinEquiv.symm i)) = ∏ i, ∏ j, g ⟨i,j⟩
  exact (Equiv.prod_comp (finSigmaFinEquiv (n := fun i => (Bs i).count)).symm g).trans
    (Fintype.prod_sigma g)

theorem charge_flatten (Bs : Fin k → Block n m) (j : Fin m) :
    charge (flatten Bs) j = ∑ i, charge (Bs i) j := by
  let g : ((i : Fin k) × Fin (Bs i).count) → ℤ :=
    fun ix => R.incidence ((Bs ix.1).ports ix.2) j
  change (∑ i, g (finSigmaFinEquiv.symm i)) = ∑ i, ∑ j, g ⟨i,j⟩
  exact (Equiv.sum_comp (finSigmaFinEquiv (n := fun i => (Bs i).count)).symm g).trans
    (Fintype.sum_sigma g)

theorem phase_flatten (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (Bs : Fin k → Block n m) (z : (Fin m → Bool)) :
    phase r f (flatten Bs) z = ∏ i, phase r f (Bs i) z := by
  let g : ((i : Fin k) × Fin (Bs i).count) → AlgebraicComplex :=
    fun ix => r ^ weight (R.word ((Bs ix.1).ports ix.2) z) * f (R.word ((Bs ix.1).ports ix.2) z)
  change (∏ i, g (finSigmaFinEquiv.symm i)) = ∏ i, ∏ j, g ⟨i,j⟩
  exact (Equiv.prod_comp (finSigmaFinEquiv (n := fun i => (Bs i).count)).symm g).trans
    (Fintype.prod_sigma g)

/-- Lift every actual copy through one fixed pure-pin minor of the source. -/
def pinLift (p : Fin n → Bool ⊕ Fin l) (B : Block l m) : Block n m :=
  ⟨B.count, fun i => P.compose p (B.ports i)⟩

theorem value_pinLift {K : Type} [CommMonoid K] (f : Signature K n)
    (p : Fin n → Bool ⊕ Fin l) (B : Block l m) (z : (Fin m → Bool)) :
    value f (pinLift p B) z = value (fun x => f (P.substitute p x)) B z := by
  simp only [value, pinLift, NoIPurePhasePinCompose.word_compose]

theorem charge_pinLift (p : Fin n → Bool ⊕ Fin l) (pure : P.PurePins p)
    (B : Block l m) : charge (pinLift p B) = charge B := by
  funext j
  simp only [charge, R.total, pinLift, NoIPurePhasePinCompose.incidence_compose p pure]

theorem phase_pinLift (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (p : Fin n → Bool ⊕ Fin l) (pure : P.PurePins p) (B : Block l m) (z : (Fin m → Bool)) :
    phase r f (pinLift p B) z =
      (r ^ P.fixedWeight p) ^ B.count * phase r (fun x => f (P.substitute p x)) B z := by
  simp only [phase, pinLift, NoIPurePhasePinCompose.word_compose,
    NoIPurePhasePinCompose.weight_substitute p pure, pow_add, mul_assoc,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem pin_scalar_nonzero (r : AlgebraicComplex) (rn : r ≠ 0)
    (p : Fin n → Bool ⊕ Fin l) (B : Block l m) :
    (r ^ P.fixedWeight p) ^ B.count ≠ 0 := pow_ne_zero _ (pow_ne_zero _ rn)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlock
end
