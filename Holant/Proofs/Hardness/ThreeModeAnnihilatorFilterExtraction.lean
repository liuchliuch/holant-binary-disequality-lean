import Holant.Proofs.Hardness.ThreeModeAnnihilatorFilterSemantics

/-! The framed-list controller's actual output field division extracts the
all-first-mode coefficient, using the explicit arithmetic root enumeration. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilatorFilterExtraction
namespace A
export ThreeModeAnnihilator
  (rootIndices mode queryCount denominator differenceFilter sample)
end A
namespace F
export ThreeModeFilter (State step)
end F
namespace S
export ThreeModeAnnihilatorFilterSemantics (table iterate_stable)
end S

section Algebra
variable {K : Type} [Field K]

def spectralRoots (m : ℕ) (lam mu nu : K) : List K :=
  (A.rootIndices m).map (A.mode m lam mu nu)

@[simp] theorem spectralRoots_length (m : ℕ) (lam mu nu : K) :
    (spectralRoots m lam mu nu).length=(A.rootIndices m).length := by simp [spectralRoots]

def initial (m : ℕ) (lam mu nu : K) (values : ℕ → K) : F.State K :=
  ((spectralRoots m lam mu nu,
      S.table ((spectralRoots m lam mu nu).length+1) values),(lam^m,lam^m))

/-- The primitive finish operation reads the sole remaining answer and divides
by the denominator that the same controller accumulated. -/
def finalValue (m : ℕ) (lam mu nu : K) (values : ℕ → K) (rounds : ℕ) : K :=
  let s := F.step^[rounds] (initial m lam mu nu values)
  s.1.2.getD 0 0 / s.2.2

/-- Full state identification; no separate algebraic denominator oracle is used. -/
theorem state_eq (m : ℕ) (lam mu nu : K) (values : ℕ → K) (rounds : ℕ)
    (hrounds : (A.rootIndices m).length ≤ rounds) :
    F.step^[rounds] (initial m lam mu nu values) =
      (([],[A.differenceFilter (spectralRoots m lam mu nu) values 0]),
        (lam^m,A.denominator m lam mu nu)) := by
  unfold initial
  rw [S.iterate_stable _ _ _ _ _ (by simpa using hrounds)]
  rw [spectralRoots, ThreeModeAnnihilator.enumerated_product m lam mu nu (A.rootIndices m)
    (ThreeModeAnnihilator.rootIndices_nodup m) (ThreeModeAnnihilator.rootIndices_toFinset m)]
  rfl

theorem finalValue_eq (m : ℕ) (lam mu nu : K) (values : ℕ → K) (rounds : ℕ)
    (hrounds : (A.rootIndices m).length ≤ rounds) :
    finalValue m lam mu nu values rounds =
      A.differenceFilter (spectralRoots m lam mu nu) values 0 / A.denominator m lam mu nu := by
  unfold finalValue
  rw [state_eq m lam mu nu values rounds hrounds]
  rfl

@[simp] theorem finalValue_zero (lam mu nu : K) (values : ℕ → K) (rounds : ℕ) :
    finalValue 0 lam mu nu values rounds = values 0 := by
  rw [finalValue_eq _ _ _ _ _ _ (by simp)]
  simp [spectralRoots]

end Algebra

section Normed
variable {K : Type} [NormedField K]

theorem finalValue_sample {m : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖) (c : ℕ × ℕ → K)
    (rounds : ℕ) (hrounds : (A.rootIndices m).length ≤ rounds) :
    finalValue m lam mu nu (A.sample m lam mu nu c) rounds = c (0,0) := by
  rw [finalValue_eq _ _ _ _ _ _ hrounds]
  rw [spectralRoots, ThreeModeAnnihilator.differenceFilter_rootIndices]
  exact mul_div_cancel_right₀ _ (ThreeModeAnnihilator.denominator_ne_zero hmu hnu)

/-- Only the values of the finitely many actual queried lengths are assumed. -/
theorem finalValue_actual {m : ℕ} {lam mu nu : K}
    (hmu : ‖mu‖ < ‖lam‖) (hnu : ‖nu‖ < ‖lam‖)
    (c : ℕ × ℕ → K) (values : ℕ → K)
    (hvalues : ∀ k < A.queryCount m lam mu nu, values k = A.sample m lam mu nu c k)
    (rounds : ℕ) (hrounds : (A.rootIndices m).length ≤ rounds) :
    finalValue m lam mu nu values rounds = c (0,0) := by
  rw [finalValue_eq _ _ _ _ _ _ hrounds]
  have hdiff : A.differenceFilter (spectralRoots m lam mu nu) values 0 =
      A.differenceFilter (spectralRoots m lam mu nu) (A.sample m lam mu nu c) 0 := by
    apply ThreeModeAnnihilator.differenceFilter_congr
    intro k hk hk'
    apply hvalues
    rw [← ThreeModeAnnihilator.rootIndices_length_add_one]
    simpa using Nat.lt_succ_of_le (by simpa using hk' : k ≤ (A.rootIndices m).length)
  rw [hdiff, spectralRoots, ThreeModeAnnihilator.differenceFilter_rootIndices]
  exact mul_div_cancel_right₀ _ (ThreeModeAnnihilator.denominator_ne_zero hmu hnu)

end Normed
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilatorFilterExtraction
