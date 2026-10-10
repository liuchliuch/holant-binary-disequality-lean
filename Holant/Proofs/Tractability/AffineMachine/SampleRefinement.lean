import Holant.Proofs.Tractability.AffineMachine.DensePrograms


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.SampleRefinement

open Holant.Tractable AffinePhase TwoTranslate EncodedTable

def assignment (n : ℕ) (m : SamplePrograms.Mask) : Word n := fun j => SamplePrograms.at m j.val

@[simp] theorem origin_assignment (n : ℕ) : assignment n SamplePrograms.origin = origin n := by
  funext j; simp [assignment, SamplePrograms.at, SamplePrograms.origin, origin]

@[simp] theorem single_assignment {n : ℕ} (i : Fin n) :
    assignment n (SamplePrograms.single i.val) = basis i := by
  funext j
  simp [assignment, SamplePrograms.at, SamplePrograms.single, basis, eq_comm, Fin.ext_iff]

@[simp] theorem pair_assignment {n : ℕ} (i j : Fin n) :
    assignment n (SamplePrograms.pair i.val j.val) = AffinePhase.xor (basis i) (basis j) := by
  funext k
  simp [assignment, SamplePrograms.at, SamplePrograms.pair, basis, AffinePhase.xor, eq_comm, Fin.ext_iff]

@[simp] theorem word_eq (n : ℕ) (m : SamplePrograms.Mask) :
    DensePrograms.word n m = List.ofFn (assignment n m) := DensePrograms.range_map _ _

def storedPhase {n : ℕ} (Q : QuadraticPhase n) : Phase :=
  (Q.constant, List.ofFn Q.linear, List.ofFn (fun j => List.ofFn (Q.mixed j)))

def sampled {n : ℕ} (q : Word n → ZMod 4) : Phase :=
  TabulatePhase.value (fun _ : Unit => n) (fun _ m => q (assignment n m)) ()

theorem sampled_eq {n : ℕ} (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) :
    sampled q = storedPhase (FiniteCore.reconstruct q hq) := by
  rw [FiniteCore.reconstruct_eq]
  simp [sampled, storedPhase, TabulatePhase.value, Reconstruction.coefficients,
    Reconstruction.mixedCoefficient, DensePrograms.range_map]
  rfl

theorem stored_regular {n : ℕ} (rs : List Row)
    (hr : ∀ r ∈ rs, r.2.length = n) (Q : QuadraticPhase n) :
    Regular (n, rs, storedPhase Q) := by
  refine ⟨hr, by simp [storedPhase], by simp [storedPhase], ?_, ?_⟩
  · intro r h
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    simp
  · intro j k hjk
    simpa [mixed, storedPhase] using Q.even_mixed j k hjk

theorem stored_phase {n : ℕ} (rs : List Row)
    (hr : ∀ r ∈ rs, r.2.length = n) (Q : QuadraticPhase n) :
    phase (n, rs, storedPhase Q) (stored_regular rs hr Q) = Q := by
  cases Q
  simp [phase, constant, linear, mixed, storedPhase]

theorem sampled_regular {n : ℕ} (rs : List Row) (hr : ∀ r ∈ rs, r.2.length = n)
    (q : Word n → ZMod 4) (hq : ∀ z u v w, thirdDifference q z u v w = 0) :
    Regular (n, rs, sampled q) := by
  rw [sampled_eq q hq]
  exact stored_regular rs hr _

/-- Byte-table reconstruction computes exactly the old kernel's phase function,
including mixed diagonal samples; evaluation still uses only the upper triangle. -/
theorem sampled_eval {n : ℕ} (rs : List Row) (hr : ∀ r ∈ rs, r.2.length = n)
    (q : Word n → ZMod 4) (hq : ∀ z u v w, thirdDifference q z u v w = 0)
    (x : Word n) :
    (phase (n, rs, sampled q) (sampled_regular rs hr q hq)).eval x = q x := by
  have hs : ∀ (P : Phase) (he : P = storedPhase (FiniteCore.reconstruct q hq))
      (hP : Regular (n, rs, P)), (phase (n, rs, P) hP).eval x = q x := by
    intro P he hP
    subst P
    rw [stored_phase rs hr, FiniteCore.reconstruct_eq]
    exact Reconstruction.eval_coefficients q hq x
  exact hs _ (sampled_eq q hq) (sampled_regular rs hr q hq)

theorem quadratic_sampled_eval {n : ℕ} (Q : QuadraticPhase n) (x : Word n) :
    DensePrograms.phaseValue ((n, [], sampled Q.eval), List.ofFn x) = Q.eval x := by
  have hq := quadratic_thirdDifference Q
  have hr : ∀ r ∈ ([] : List Row), r.2.length = n := by simp
  rw [DensePrograms.phaseValue_exact _ (sampled_regular [] hr Q.eval hq)]
  simpa using sampled_eval [] hr Q.eval hq x

end Holant.LocalDrafts.Tractability.AffineMachine.SampleRefinement
