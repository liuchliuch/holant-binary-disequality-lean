import Holant.Proofs.Algorithms.TransformRecognition.StandardRootCodes
import Holant.Proofs.Algorithms.TransformRecognition.SparseTransform


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalVariableLayout
open Holant.LocalDrafts.EffectiveAlgebraic Holant.Tractable

abbrev Extra (m q : ℕ) := q+(m+3)
abbrev Width (m q : ℕ) := 5+Extra m q

def matrix (m q : ℕ) (i : Fin 5) : Fin (Width m q) := Fin.castAdd (Extra m q) i
def parameter (m q : ℕ) (i : Fin q) : Fin (Width m q) :=
  Fin.natAdd 5 (Fin.castAdd (m+3) i)
def original (m q : ℕ) (i : Fin m) : Fin (Width m q) :=
  Fin.natAdd 5 (Fin.natAdd q (Fin.castAdd 3 i))
def special (m q : ℕ) (i : Fin 3) : Fin (Width m q) :=
  Fin.natAdd 5 (Fin.natAdd q (Fin.natAdd m i))
def binding (m q : ℕ) : Fin (m+2) → Fin (Width m q) :=
  Fin.addCases (original m q) (fun i => special m q i.castSucc)

def descriptors {m : ℕ} (input : Fin m → RootCode) : Fin (m+2) → RootCode :=
  Fin.addCases input StandardRootCodes.descriptors

def fill {E : Type*} {m q : ℕ} (a : Fin 5 → E) (p : Fin q → E)
    (w : Fin m → E) (c : Fin 3 → E) : Fin (Width m q) → E :=
  Fin.addCases a (Fin.addCases p (Fin.addCases w c))

@[simp] theorem fill_matrix {E : Type*} {m q : ℕ} (a : Fin 5 → E) (p : Fin q → E)
    (w : Fin m → E) (c : Fin 3 → E) (i : Fin 5) :
    fill a p w c (matrix m q i)=a i := by simp [fill,matrix]
@[simp] theorem fill_parameter {E : Type*} {m q : ℕ} (a : Fin 5 → E) (p : Fin q → E)
    (w : Fin m → E) (c : Fin 3 → E) (i : Fin q) :
    fill a p w c (parameter m q i)=p i := by simp [fill,parameter]
@[simp] theorem fill_original {E : Type*} {m q : ℕ} (a : Fin 5 → E) (p : Fin q → E)
    (w : Fin m → E) (c : Fin 3 → E) (i : Fin m) :
    fill a p w c (original m q i)=w i := by simp [fill,original]
@[simp] theorem fill_special {E : Type*} {m q : ℕ} (a : Fin 5 → E) (p : Fin q → E)
    (w : Fin m → E) (c : Fin 3 → E) (i : Fin 3) :
    fill a p w c (special m q i)=c i := by simp [fill,special]

theorem parameter_original_ne {m q : ℕ} (i : Fin q) (j : Fin m) :
    parameter m q i ≠ original m q j := by
  intro h
  have he := congrArg Fin.val h
  have hi := i.isLt
  simp [parameter,original] at he
  omega

theorem original_special_ne {m q : ℕ} (i : Fin m) (j : Fin 3) :
    original m q i ≠ special m q j := by
  intro h
  have he := congrArg Fin.val h
  have hi := i.isLt
  simp [original,special] at he
  omega

noncomputable section

def constants : Fin 3 → ℂ := ![Complex.I,(Real.sqrt 2 : ℂ),(zetaEight : ℂ)]
def boundValues {m : ℕ} (w : Fin m → ℂ) : Fin (m+2) → ℂ :=
  Fin.addCases w StandardRootCodes.values

theorem descriptors_represents {m : ℕ} (input : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (input i).Represents (w i)) :
    ∀ i, (descriptors input i).Represents (boundValues w i) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa [descriptors,boundValues] using hw i
  | right i => simpa [descriptors,boundValues] using StandardRootCodes.represents i

theorem fill_binding {m q : ℕ} (a : Fin 5 → ℂ) (p : Fin q → ℂ) (w : Fin m → ℂ)
    (i : Fin (m+2)) : fill a p w constants (binding m q i)=boundValues w i := by
  induction i using Fin.addCases with
  | left i => simp [binding,boundValues]
  | right i =>
    fin_cases i <;> simp [binding,boundValues,constants,StandardRootCodes.values]

theorem binding_original {m q : ℕ} (z : Fin (Width m q) → ℂ) (w : Fin m → ℂ)
    (hb : ∀ i, z (binding m q i)=boundValues w i) (i : Fin m) :
    z (original m q i)=w i := by
  simpa [binding,boundValues] using hb (Fin.castAdd 2 i)

theorem binding_imaginary {m q : ℕ} (z : Fin (Width m q) → ℂ) (w : Fin m → ℂ)
    (hb : ∀ i, z (binding m q i)=boundValues w i) :
    z (special m q 0)=Complex.I := by
  simpa [binding,boundValues,StandardRootCodes.values] using hb (Fin.natAdd m 0)

theorem binding_sqrt {m q : ℕ} (z : Fin (Width m q) → ℂ) (w : Fin m → ℂ)
    (hb : ∀ i, z (binding m q i)=boundValues w i) :
    z (special m q 1)=(Real.sqrt 2 : ℂ) := by
  simpa [binding,boundValues,StandardRootCodes.values] using hb (Fin.natAdd m 1)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalVariableLayout
