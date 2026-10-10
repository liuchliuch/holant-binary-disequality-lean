import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseBlock
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceTranslation
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalAffine

/-! Actual signed transformations and coordinate renamings act on every
original-labelled row of a finite block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlock
open Holant Holant.Tractable
open scoped BigOperators
namespace T
export NoIPurePhaseIncidencePorts.P (Transform image linearWord)
export NoIPurePhaseIncidencePorts.R (transformed transformed_word)
export NoIPurePhaseIncidenceCore.C (codeSeven)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n m l : ℕ}

def renamePort (p : Fin n → R.Port m) (e : Fin m → Fin l) (i : Fin n) : R.Port l :=
  match p i with
  | .inl b => .inl b
  | .inr (j,s) => .inr (e j,s)

theorem renamePort_word (p : Fin n → R.Port m) (e : Fin m → Fin l) (z : Fin l → Bool) :
    R.word (renamePort p e) z = R.word p (fun j => z (e j)) := by
  funext i
  cases h : p i <;> simp [R.word, renamePort, h]

theorem renamePort_incidence (p : Fin n → R.Port m) (e : Fin m → Fin l) (j : Fin l) :
    R.incidence (renamePort p e) j = ∑ k, if e k = j then R.incidence p k else 0 := by
  unfold R.incidence
  have distribute (h : Prop) [Decidable h] (g : Fin n → ℤ) :
      (if h then ∑ i, g i else 0) = ∑ i, if h then g i else 0 := by
    split_ifs <;> simp
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p i with
  | inl b => simp [renamePort, hp]
  | inr v =>
    rcases v with ⟨k,s⟩
    rw [Finset.sum_eq_single k]
    · simp [renamePort, hp]
    · intro a _ ha
      simp [Ne.symm ha]
    · simp

def rename (B : Block n m) (e : Fin m → Fin l) : Block n l :=
  ⟨B.count, fun i => renamePort (B.ports i) e⟩

theorem value_rename {K : Type} [CommMonoid K] (f : Signature K n)
    (B : Block n m) (e : Fin m → Fin l) (z : Fin l → Bool) :
    value f (rename B e) z = value f B (fun j => z (e j)) := by
  simp only [value, rename, renamePort_word]

theorem phase_rename (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n m) (e : Fin m → Fin l) (z : Fin l → Bool) :
    phase r f (rename B e) z = phase r f B (fun j => z (e j)) := by
  simp only [phase, rename, renamePort_word]

theorem charge_rename (B : Block n m) (e : Fin m → Fin l) (j : Fin l) :
    charge (rename B e) j = ∑ k, if e k = j then charge B k else 0 := by
  unfold charge R.total rename
  simp only [renamePort_incidence]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : e k = j <;> simp [h]

def transform (B : Block n 7) (t : T.Transform) : Block n 7 :=
  ⟨B.count, fun i => T.transformed (B.ports i) t⟩

theorem value_transform_code {K : Type} [CommMonoid K] (f : Signature K n)
    (B : Block n 7) (t : T.Transform) (x : Fin 3 → Bool) :
    value f (transform B t) (T.codeSeven x) = value f B (T.codeSeven (T.linearWord t x)) := by
  simp only [value, transform, T.transformed_word]

theorem phase_transform_code (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n 7) (t : T.Transform) (x : Fin 3 → Bool) :
    phase r f (transform B t) (T.codeSeven x) = phase r f B (T.codeSeven (T.linearWord t x)) := by
  simp only [phase, transform, T.transformed_word]

theorem charge_transform (B : Block n 7) (t : T.Transform) (j : Fin 7) :
    charge (transform B t) j = ∑ k, if T.image t k = j.succ then charge B k else 0 := by
  unfold charge R.total transform
  simp only [NoIPurePhaseIncidencePorts.transformed_incidence]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : T.image t k = j.succ <;> simp [h]

def transformPorts (t : T.Transform) : Fin 7 → R.Port 7 :=
  T.transformed (fun j => Sum.inr (j,false)) t

theorem transform_word (p : Fin n → R.Port 7) (t : T.Transform) (z : Fin 7 → Bool) :
    R.word (T.transformed p t) z = R.word p (R.word (transformPorts t) z) := by
  funext i
  cases hp : p i with
  | inl b => simp [R.word, T.transformed, hp]
  | inr v =>
    rcases v with ⟨j,s⟩
    simp only [R.word, T.transformed, hp, transformPorts]
    split_ifs <;> cases s <;> simp

theorem word_affine (p : Fin n → R.Port m) : TwoTranslate.IsAffineMap (R.word p) := by
  intro x y
  funext i
  cases h : p i with
  | inl b => cases b <;> simp [R.word, h, AffinePhase.xor]
  | inr v =>
    rcases v with ⟨j,s⟩
    cases s <;> cases x j <;> cases y j <;>
      simp [R.word, h, AffinePhase.xor, AffinePhase.origin]

theorem value_transform {K : Type} [CommMonoid K] (f : Signature K n)
    (B : Block n 7) (t : T.Transform) (z : Fin 7 → Bool) :
    value f (transform B t) z = value f B (R.word (transformPorts t) z) := by
  simp only [value, transform, transform_word]

theorem phase_transform (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n 7) (t : T.Transform) (z : Fin 7 → Bool) :
    phase r f (transform B t) z = phase r f B (R.word (transformPorts t) z) := by
  simp only [phase, transform, transform_word]

theorem transform_affine (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n 7) (t : T.Transform) (good : Affine (phase r f B)) :
    Affine (phase r f (transform B t)) := by
  have eqn := funext (phase_transform r f B t)
  rw [eqn]
  exact good.precompose _ (word_affine (transformPorts t))

theorem transform_full_code {K : Type} [CommMonoidWithZero K] (f : Signature K n)
    (B : Block n 7) (t : T.Transform)
    (full : ∀ x : Fin 3 → Bool, value f B (T.codeSeven x) ≠ 0) :
    ∀ x : Fin 3 → Bool, value f (transform B t) (T.codeSeven x) ≠ 0 := by
  intro x
  rw [value_transform_code]
  exact full _

def translate (B : Block n m) (u : Fin m → Bool) : Block n m :=
  ⟨B.count, fun i => NoIPurePhaseIncidenceTranslation.ports (B.ports i) u⟩

theorem value_translate {K : Type} [CommMonoid K] (f : Signature K n)
    (B : Block n m) (u z : Fin m → Bool) :
    value f (translate B u) z = value f B (fun j => u j ^^ z j) := by
  simp only [value, translate, NoIPurePhaseIncidenceTranslation.value]

theorem phase_translate (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n m) (u z : Fin m → Bool) :
    phase r f (translate B u) z = phase r f B (fun j => u j ^^ z j) := by
  simp only [phase, translate, NoIPurePhaseIncidenceTranslation.value]

theorem charge_translate (B : Block n m) (u : Fin m → Bool) (j : Fin m) :
    charge (translate B u) j = if u j then -(charge B j) else charge B j := by
  simp only [charge, R.total, translate, NoIPurePhaseIncidenceTranslation.incidence]
  cases u j <;> simp

theorem xor_affine (u : Fin m → Bool) :
    TwoTranslate.IsAffineMap (fun z : Fin m → Bool => fun j => u j ^^ z j) :=
  word_affine (fun j => Sum.inr (j,u j))

theorem translate_affine (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n m) (u : Fin m → Bool) (good : Affine (phase r f B)) :
    Affine (phase r f (translate B u)) := by
  have eqn := funext (phase_translate r f B u)
  rw [eqn]
  exact good.precompose _ (xor_affine u)

theorem value_translate_code {K : Type} [CommMonoid K] (f : Signature K n)
    (B : Block n 7) (u x : Fin 3 → Bool) :
    value f (translate B (T.codeSeven u)) (T.codeSeven x) =
      value f B (T.codeSeven (fun j => u j ^^ x j)) := by
  rw [value_translate, NoIPurePhaseIncidenceTranslation.code_translation]

theorem phase_translate_code (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n 7) (u x : Fin 3 → Bool) :
    phase r f (translate B (T.codeSeven u)) (T.codeSeven x) =
      phase r f B (T.codeSeven (fun j => u j ^^ x j)) := by
  rw [phase_translate, NoIPurePhaseIncidenceTranslation.code_translation]

theorem translate_full_code {K : Type} [CommMonoidWithZero K] (f : Signature K n)
    (B : Block n 7) (u : Fin 3 → Bool)
    (full : ∀ x : Fin 3 → Bool, value f B (T.codeSeven x) ≠ 0) :
    ∀ x : Fin 3 → Bool, value f (translate B (T.codeSeven u)) (T.codeSeven x) ≠ 0 := by
  intro x
  rw [value_translate_code]
  exact full _

theorem xor_precompose_affine_iff (g : Signature AlgebraicComplex m) (u : Fin m → Bool) :
    Affine (fun z => g (fun j => u j ^^ z j)) ↔ Affine g := by
  constructor
  · intro good
    convert good.precompose _ (xor_affine u) using 1
    funext z
    congr 1
    funext j
    dsimp only
    cases u j <;> cases z j <;> rfl
  · intro good
    exact good.precompose _ (xor_affine u)

theorem phase_translate_code_affine_iff (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : Block n 7) (u : Fin 3 → Bool) :
    Affine (fun x => phase r f (translate B (T.codeSeven u)) (T.codeSeven x)) ↔
      Affine (fun x => phase r f B (T.codeSeven x)) := by
  simp only [phase_translate_code]
  exact xor_precompose_affine_iff (fun x => phase r f B (T.codeSeven x)) u

theorem legal_value (f : Signature AlgebraicComplex n)
    (legal : NoIPurePhaseLegalAffine.LegalAffine f) (B : Block n m)
    (zero : ∀ j, charge B j % 4 = 0) : Affine (value f B) :=
  legal m B.count B.ports zero

theorem legal_phase (f : Signature AlgebraicComplex n)
    (legal : NoIPurePhaseLegalAffine.LegalAffine f) (r : AlgebraicComplex)
    (rn : r ≠ 0) (root : r ^ 16 = 1) (B : Block n m)
    (zero : ∀ j, charge B j % 4 = 0) : Affine (phase r f B) :=
  (phase_affine_iff r rn root f B zero).mpr (legal_value f legal B zero)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlock
end
