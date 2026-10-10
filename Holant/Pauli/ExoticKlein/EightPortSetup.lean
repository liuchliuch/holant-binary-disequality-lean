import Holant.Pauli.ExoticKlein.Matching
import Holant.Pauli.ProjectiveDetermination.Ports

/-! The literal eight-port normal form and its two specified residual matchings.
The labels are the additive group F₂² and every port keeps its original index. -/
namespace Holant.Pauli.ExoticKlein.EightPort
noncomputable section
open scoped BigOperators
open ProjectiveDetermination

/-- An actual four-term normal form, with all coefficient scales retained. -/
def normalForm (lambda : Label → ℂ) (A1 A2 A3 : Label ≃+ Label) : Signature ℂ 8 :=
  fun x => ∑ g, lambda g * E g (x 0) (x 1) * E (A1 g) (x 2) (x 3) *
    E (A2 g) (x 4) (x 5) * E (A3 g) (x 6) (x 7)

/-- Bilinear contraction against the actual Frobenius dual on two original ports. -/
def pairCard (r s : Fin 8) (a : Label) (h : Signature ℂ 8) : Tensor ℂ (Rest r s) :=
  fun z => ∑ u : Bool, ∑ v : Bool, dual a u v * h (fill r s u v z)

private def port35Fun (p : Fin 3 × Bool) : Rest (2 : Fin 8) 4 :=
  if p.2 then ![⟨1,by decide⟩,⟨5,by decide⟩,⟨7,by decide⟩] p.1
  else ![⟨0,by decide⟩,⟨3,by decide⟩,⟨6,by decide⟩] p.1

private def port45Fun (p : Fin 3 × Bool) : Rest (3 : Fin 8) 4 :=
  if p.2 then ![⟨1,by decide⟩,⟨5,by decide⟩,⟨7,by decide⟩] p.1
  else ![⟨0,by decide⟩,⟨2,by decide⟩,⟨6,by decide⟩] p.1

private def ports35 : (Fin 3 × Bool) ≃ Rest (2 : Fin 8) 4 :=
  Equiv.ofBijective port35Fun (by decide)

private def ports45 : (Fin 3 × Bool) ≃ Rest (3 : Fin 8) 4 :=
  Equiv.ofBijective port45Fun (by decide)

/-- The ordered residual edges are (0,1), (3,5), and (6,7). -/
def residual35 : Matching (Rest (2 : Fin 8) 4) 3 := ⟨ports35⟩

/-- The ordered residual edges are (0,1), (2,5), and (6,7). -/
def residual45 : Matching (Rest (3 : Fin 8) 4) 3 := ⟨ports45⟩

def D35 (A1 A2 : Label ≃+ Label) (g : Label) : Label := theta (A1 g) + A2 g

def D45 (A1 A2 : Label ≃+ Label) (g : Label) : Label := A1 g + A2 g

def labelTriple (D : Label → Label) (A3 : Label ≃+ Label) (g : Label) : Fin 3 → Label :=
  ![g,D g,A3 g]

def weight35 (lambda : Label → ℂ) (A1 A2 : Label ≃+ Label) (g : Label) : ℂ :=
  lambda g * (1/2 : ℂ) * transposeScalar (A1 g) * omega (theta (A1 g)) (A2 g)

def weight45 (lambda : Label → ℂ) (A1 A2 : Label ≃+ Label) (g : Label) : ℂ :=
  lambda g * (1/2 : ℂ) * omega (A1 g) (A2 g)

theorem weight35_ne_zero (lambda : Label → ℂ) (A1 A2 : Label ≃+ Label)
    (hlambda : ∀ g, lambda g ≠ 0) (g : Label) : weight35 lambda A1 A2 g ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hlambda g) (by norm_num))
    (transposeScalar_ne_zero _)) (omega_ne_zero _ _)

theorem weight45_ne_zero (lambda : Label → ℂ) (A1 A2 : Label ≃+ Label)
    (hlambda : ∀ g, lambda g ≠ 0) (g : Label) : weight45 lambda A1 A2 g ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (hlambda g) (by norm_num)) (omega_ne_zero _ _)

@[simp] theorem residual35_tensor (labels : Fin 3 → Label) (z : Rest (2 : Fin 8) 4 → Bool) :
    residual35.tensor labels z =
      E (labels 0) (z ⟨0,by decide⟩) (z ⟨1,by decide⟩) *
      E (labels 1) (z ⟨3,by decide⟩) (z ⟨5,by decide⟩) *
      E (labels 2) (z ⟨6,by decide⟩) (z ⟨7,by decide⟩) := by
  simp [Matching.tensor,residual35,ports35,port35Fun,Fin.prod_univ_succ,mul_assoc]

@[simp] theorem residual45_tensor (labels : Fin 3 → Label) (z : Rest (3 : Fin 8) 4 → Bool) :
    residual45.tensor labels z =
      E (labels 0) (z ⟨0,by decide⟩) (z ⟨1,by decide⟩) *
      E (labels 1) (z ⟨2,by decide⟩) (z ⟨5,by decide⟩) *
      E (labels 2) (z ⟨6,by decide⟩) (z ⟨7,by decide⟩) := by
  simp [Matching.tensor,residual45,ports45,port45Fun,Fin.prod_univ_succ,mul_assoc]

end
end Holant.Pauli.ExoticKlein.EightPort
