import Holant.Tractable.AffinePhase.Roots
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.OfFn


namespace Holant.LocalDrafts.MainChain.TransformRecognition.AffineNormalForm
open Holant.Tractable
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Equation (n : ℕ) := (Fin n → ZMod 2) × ZMod 2
abbrev SupportCode (n : ℕ) := Finset (Equation n)
abbrev PhaseCode (n : ℕ) := ZMod 4 × (Fin n → ZMod 4) × (Fin n → Fin n → Bool)
abbrev Code (n : ℕ) := SupportCode n × PhaseCode n

def equationHolds {n : ℕ} (e : Equation n) (x : Fin n → Bool) : Prop :=
  (∑ j, e.1 j * bitValue (ZMod 2) (x j))=e.2

def supportHolds {n : ℕ} (C : SupportCode n) (x : Fin n → Bool) : Prop :=
  ∀ e ∈ C, equationHolds e x

def compress {n : ℕ} (S : AffineSystem n) : SupportCode n :=
  Finset.univ.image (fun r => (S.matrix r,S.rhs r))

theorem compress_holds {n : ℕ} (S : AffineSystem n) (x : Fin n → Bool) :
    supportHolds (compress S) x ↔ S.Holds x := by
  simp [supportHolds,compress,equationHolds,AffineSystem.Holds]

def system {n : ℕ} (C : SupportCode n) : AffineSystem n where
  rows := C.toList.length
  matrix r := (C.toList.get r).1
  rhs r := (C.toList.get r).2

theorem system_holds {n : ℕ} (C : SupportCode n) (x : Fin n → Bool) :
    (system C).Holds x ↔ supportHolds C x := by
  constructor
  · intro h e he
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (show e ∈ C.toList by simpa using he)
    have hr := h i
    change equationHolds (C.toList.get i) x at hr
    rwa [hi] at hr
  · intro h i
    exact h (C.toList.get i) (by simpa using List.get_mem C.toList i)

theorem system_rows_le {n : ℕ} (C : SupportCode n) :
    (system C).rows ≤ Fintype.card (Equation n) := by
  simpa [system] using Finset.card_le_univ C

def phase {n : ℕ} (C : PhaseCode n) : QuadraticPhase n where
  constant := C.1
  linear := C.2.1
  mixed j k := if C.2.2 j k then 2 else 0
  even_mixed j k _ := by cases h : C.2.2 j k <;> simp [h]

def encodePhase {n : ℕ} (Q : QuadraticPhase n) : PhaseCode n :=
  (Q.constant,Q.linear,fun j k => decide (Q.mixed j k=2))

theorem phase_mixed {n : ℕ} (Q : QuadraticPhase n) (j k : Fin n) (hjk : j<k) :
    (phase (encodePhase Q)).mixed j k=Q.mixed j k := by
  rcases Q.even_mixed j k hjk with h | h <;>
    simp [phase,encodePhase,h,show (0 : ZMod 4) ≠ 2 by decide]

theorem phase_eval {n : ℕ} (Q : QuadraticPhase n) (x : Fin n → Bool) :
    (phase (encodePhase Q)).eval x=Q.eval x := by
  unfold QuadraticPhase.eval
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hjk
  · rw [phase_mixed Q j k hjk]
  · rfl

def formula {n : ℕ} (C : Code n) (c : AlgebraicComplex) : Signature AlgebraicComplex n :=
  affineFormula c (system C.1) (phase C.2)

theorem formula_affine {n : ℕ} (C : Code n) (c : AlgebraicComplex) : Affine (formula C c) :=
  affine_formula c (system C.1) (phase C.2)

theorem compressed_formula {n : ℕ} (S : AffineSystem n) (Q : QuadraticPhase n)
    (c : AlgebraicComplex) : formula (compress S,encodePhase Q) c=affineFormula c S Q := by
  funext x
  simp [formula,affineFormula,system_holds,compress_holds,phase_eval]

/-- Finite combinatorial type plus one scalar, including zero/nullary cases. -/
theorem affine_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    Affine f ↔ ∃ C : Code n, ∃ c : AlgebraicComplex, f=formula C c := by
  constructor
  · rintro (rfl | ⟨c,hc,S,Q,hf⟩)
    · refine ⟨(∅,0,(fun _ => 0),(fun _ _ => false)),0,?_⟩
      funext x
      simp [formula,affineFormula]
    · exact ⟨(compress S,encodePhase Q),c,hf.trans (compressed_formula S Q c).symm⟩
  · rintro ⟨C,c,rfl⟩
    exact formula_affine C c

def allCodes (n : ℕ) : Finset (Code n) := Finset.univ

theorem finite_enumeration {n : ℕ} (f : Signature AlgebraicComplex n) :
    Affine f ↔ ∃ C ∈ allCodes n, ∃ c : AlgebraicComplex, f=formula C c := by
  simpa [allCodes] using affine_iff f

/-- The only free coefficient occurs linearly in each selected table entry. -/
theorem entry_formula {n : ℕ} (C : Code n) (c : AlgebraicComplex) (x : Fin n → Bool) :
    formula C c x=c * (if supportHolds C.1 x then fourthRootPhase ((phase C.2).eval x) else 0) := by
  simp [formula,affineFormula,system_holds,mul_ite]

end
end Holant.LocalDrafts.MainChain.TransformRecognition.AffineNormalForm
